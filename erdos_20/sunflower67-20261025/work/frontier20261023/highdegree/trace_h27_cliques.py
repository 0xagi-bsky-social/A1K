#!/usr/bin/env python3
"""Solver-free, deadline-bounded H27 clique separation on saved trace weights.

Examples:
  python3 trace_h27_cliques.py --receipt saved.json --output cuts.json
  python3 trace_h27_cliques.py --receipt saved.json --fixed-members fixed.json \
      --extend --seconds 10 --output cuts.json

An explicit fixed document may be an array of four-set masks, or an object
with fixed_members (alias fixed), represented_points and excluded_points.
Without it, geometry.link/root and the receipt's selected marker/assigned_z
provide fixed actual members. Actual membership is a mathematical premise.
No LP, model import, or independent original-model reconstruction occurs.
"""
from __future__ import annotations

import argparse
from decimal import Decimal
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import time


class BudgetEnd(Exception):
    pass


class Budget:
    def __init__(self, seconds):
        self.start = time.monotonic()
        self.deadline = self.start + seconds

    def check(self):
        if time.monotonic() >= self.deadline:
            raise BudgetEnd('deadline')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def strict_int(x, what):
    if type(x) is not int or x < 0:
        raise ValueError(f'{what} must be a nonnegative integer')
    return x


def points(mask):
    result = set()
    while mask:
        bit = mask & -mask
        result.add(bit.bit_length() - 1)
        mask ^= bit
    return result


def point_mask(values, what):
    if not isinstance(values, list):
        raise ValueError(f'{what} must be an array of point indices')
    values = [strict_int(x, what) for x in values]
    if len(set(values)) != len(values) or any(v > 10000 for v in values):
        raise ValueError(f'{what} contains duplicate or excessively large indices')
    return sum(1 << v for v in values)


def load(path):
    return json.loads(Path(path).read_text(), parse_float=Decimal)


def extract_input(receipt, fixed_document):
    g = receipt.get('geometry', {})
    excluded = 1 << strict_int(g['root'], 'root') if 'root' in g else 0
    represented = point_mask(g.get('Y', []) + g.get('Z', []), 'geometry points')
    actual_premises = []
    if fixed_document is not None:
        if isinstance(fixed_document, dict):
            fixed = fixed_document.get('fixed_members', fixed_document.get('fixed'))
            if 'excluded_points' in fixed_document:
                excluded = point_mask(fixed_document['excluded_points'], 'excluded_points')
            if 'represented_points' in fixed_document:
                represented = point_mask(fixed_document['represented_points'], 'represented_points')
        else:
            fixed = fixed_document
        actual_premises.append('Every explicitly supplied fixed four-set is an actual member of F.')
    else:
        if not g or 'root' not in g or 'link' not in g:
            raise ValueError('receipt needs root/link geometry or an explicit fixed-member document')
        fixed = []
        for t in g['link']:
            t = strict_int(t, 'root link mask')
            if t.bit_count() != 3 or t & excluded:
                raise ValueError('root link entries must be three-sets avoiding the root')
            fixed.append(t | excluded)
        case = receipt.get('case', 'none')
        if case not in g.get('records', {}):
            raise ValueError('selected case is missing from geometry.records')
        marker = g['records'][case].get('marker')
        if marker is not None:
            fixed.append(strict_int(marker, 'actual marker'))
        assigned = receipt.get('assigned_z')
        if assigned is not None:
            if not isinstance(assigned, list):
                raise ValueError('assigned_z must be an array or null')
            fixed.extend(assigned)
        actual_premises.append('Recorded root cones, selected case marker, and assigned_z four-sets are actual members of F.')
        # Include each actual marker point; never merely assume a free exterior
        # point is in the represented universe because its label was advertised.
        for b in fixed:
            represented |= strict_int(b, 'fixed mask') & ~excluded
    if not isinstance(fixed, list):
        raise ValueError('fixed members must be an array of integer masks')
    fixed = sorted(set(strict_int(b, 'fixed mask') for b in fixed))
    if represented & excluded:
        raise ValueError('represented and excluded point sets must be disjoint')
    if not represented:
        # With an explicit list, the available actual support is a safe default.
        for b in fixed:
            represented |= b & ~excluded
    if len(points(represented)) > 24:
        raise ValueError('at most 24 represented points are supported by this discovery tool')
    for b in fixed:
        if b.bit_count() != 4:
            raise ValueError('each fixed member must be a four-set')
        if b & ~(represented | excluded):
            raise ValueError('a fixed member has unknown support outside represented/excluded points')
    weights = {}
    for row in receipt.get('primal_trace', []):
        if not isinstance(row, list) or len(row) != 2:
            raise ValueError('primal_trace must contain [mask, weight] pairs')
        s = strict_int(row[0], 'trace mask')
        if s in weights:
            raise ValueError('duplicate trace mask in primal_trace')
        if s.bit_count() > 4 or s & ~represented:
            raise ValueError('a primal trace lies outside the represented universe or exceeds size four')
        if type(row[1]) not in (int, Decimal):
            raise ValueError('weights must be finite nonnegative JSON numbers')
        w = Fraction(row[1])
        if w < 0:
            raise ValueError('negative saved trace weights are unsupported')
        weights[s] = w
    if not weights:
        raise ValueError('receipt has no saved primal_trace entries')
    return represented, excluded, fixed, weights, actual_premises


def compatible(s, t, fixed):
    return bool(s & t) or any(not ((s | t) & b) for b in fixed)


def literal_validation(clique, fixed, represented, excluded, budget):
    """Independent set-based validation, deliberately not using compatible()."""
    us, xs = points(represented), points(excluded)
    bs = [points(b) for b in fixed]
    if us & xs or any(len(b) != 4 or not b <= us | xs for b in bs):
        raise ValueError('literal witness universe validation failed')
    ts = [points(s) for s in clique]
    if len(set(clique)) != len(clique) or any(len(t) > 4 or not t <= us for t in ts):
        raise ValueError('literal trace validation failed')
    witnesses = []
    for i, s in enumerate(ts):
        budget.check()
        for j in range(i, len(ts)):
            t = ts[j]
            shared = s.intersection(t)
            if shared:
                witnesses.append([i, j, 'point', min(shared)])
                continue
            for k, b in enumerate(bs):
                if b.isdisjoint(s.union(t)):
                    witnesses.append([i, j, 'fixed', k])
                    break
            else:
                raise ValueError(f'literal pair witness failed for trace indices {i}, {j}')
    return witnesses


def rational_record(x):
    return dict(numerator=x.numerator, denominator=x.denominator,
                decimal=str(Decimal(x.numerator) / Decimal(x.denominator)))


def separate(weights, fixed, represented, excluded, budget, tolerance, max_cliques, max_vertices):
    # Empty self-compatibility needs a fixed member. Every other diagonal
    # is automatic. We keep no vertex that fails its diagonal premise.
    vertices = sorted((s for s, w in weights.items() if w > 0 and compatible(s, s, fixed)),
                      key=lambda s: (-weights[s], s))
    if len(vertices) > max_vertices:
        raise ValueError(f'positive support exceeds --max-vertices={max_vertices}')
    adjacency = [0] * len(vertices)
    stats = dict(positive_vertices=len(vertices), search_nodes=0, maximal_cliques=0,
                 enumeration_complete=False, stop_reason=None)
    found = []

    def search(r, p, x):
        budget.check()
        stats['search_nodes'] += 1
        if not p and not x:
            stats['maximal_cliques'] += 1
            c = [vertices[i] for i in r]
            value = sum((weights[s] for s in c), Fraction())
            if value > 27 + tolerance:
                if len(found) >= max_cliques:
                    raise BudgetEnd('output-clique limit')
                c.sort()
                witnesses = literal_validation(c, fixed, represented, excluded, budget)
                found.append((c, value, witnesses))
            return
        union = p | x
        pivot = -1
        best = -1
        while union:
            bit = union & -union
            u = bit.bit_length() - 1
            score = (p & adjacency[u]).bit_count()
            if score > best:
                pivot, best = u, score
            union ^= bit
        candidates = p if pivot < 0 else p & ~adjacency[pivot]
        while candidates:
            bit = candidates & -candidates
            v = bit.bit_length() - 1
            search(r + [v], p & adjacency[v], x & adjacency[v])
            p ^= bit
            x |= bit
            candidates ^= bit

    try:
        for i, s in enumerate(vertices):
            budget.check()
            for j in range(i):
                if compatible(s, vertices[j], fixed):
                    adjacency[i] |= 1 << j
                    adjacency[j] |= 1 << i
        search([], (1 << len(vertices)) - 1, 0)
        stats['enumeration_complete'] = True
    except BudgetEnd as e:
        stats['stop_reason'] = str(e)
    found.sort(key=lambda item: (-item[1], item[0]))
    return found, stats


def extend(clique, represented, fixed, weights, budget):
    try:
        budget.check()
    except BudgetEnd:
        return clique, False
    current = set(clique)
    universe = sorted(points(represented))
    # Order is deliberately deterministic; this is a greedy extension,
    # not a claim of a maximum-weight or maximum-cardinality clique.
    candidates = [sum(1 << v for v in vs) for k in range(5)
                  for vs in itertools.combinations(universe, k)]
    candidates.sort(key=lambda s: (-weights.get(s, Fraction()), -s.bit_count(), s))
    complete = True
    try:
        for s in candidates:
            budget.check()
            if s not in current and compatible(s, s, fixed) and all(
                    compatible(s, t, fixed) for t in current):
                current.add(s)
    except BudgetEnd:
        complete = False
    return sorted(current), complete


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', required=True, type=Path)
    parser.add_argument('--fixed-members', type=Path)
    parser.add_argument('--producer-source', type=Path)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--seconds', type=float, default=5)
    parser.add_argument('--tolerance', default='0.000001')
    parser.add_argument('--max-cliques', type=int, default=1000)
    parser.add_argument('--max-vertices', type=int, default=256)
    parser.add_argument('--extend', action='store_true')
    parser.add_argument('--include-pair-witnesses', action='store_true',
                        help='store every pair witness; default stores their digest and counts')
    args = parser.parse_args()
    if not 0 < args.seconds <= 30:
        parser.error('--seconds must be in (0,30]')
    if not 1 <= args.max_cliques <= 10000 or not 1 <= args.max_vertices <= 500:
        parser.error('require 1<=max-cliques<=10000 and 1<=max-vertices<=500')
    if args.output.exists():
        parser.error('output already exists; choose a new receipt path')
    try:
        tolerance = Fraction(Decimal(args.tolerance))
        if tolerance < 0:
            raise ValueError('tolerance must be nonnegative')
        receipt = load(args.receipt)
        fixed_document = load(args.fixed_members) if args.fixed_members else None
        represented, excluded, fixed, weights, actual_premises = extract_input(receipt, fixed_document)
        producer_hash = sha(args.producer_source) if args.producer_source else None
        claimed_hash = receipt.get('source_sha256')
        if producer_hash is not None and producer_hash != claimed_hash:
            raise ValueError('supplied producer source does not match receipt source_sha256')
        budget = Budget(args.seconds)
        found, stats = separate(weights, fixed, represented, excluded, budget, tolerance,
                                args.max_cliques, args.max_vertices)
        cliques = []
        for original, value, original_witnesses in found:
            clique, witnesses, extension_complete = original, original_witnesses, None
            if args.extend:
                extended, extension_complete = extend(original, represented, fixed, weights, budget)
                try:
                    checked = literal_validation(extended, fixed, represented, excluded, budget)
                    clique, witnesses = extended, checked
                except BudgetEnd:
                    # Keep the already independently checked support clique if
                    # the extension cannot finish its independent validation.
                    extension_complete = False
            encoded = json.dumps(witnesses, separators=(',', ':')).encode()
            row = dict(trace_masks=clique, positive_support_clique=original,
                upper=27, discovery_weight=rational_record(value),
                extended_discovery_weight=rational_record(sum((weights.get(s, Fraction()) for s in clique), Fraction())),
                extension_complete=extension_complete,
                validation=dict(method='independent literal-set check',
                    pairs_including_self=len(witnesses),
                    shared_point_witnesses=sum(w[2] == 'point' for w in witnesses),
                    missed_fixed_member_witnesses=sum(w[2] == 'fixed' for w in witnesses),
                    witnesses_sha256=hashlib.sha256(encoded).hexdigest()))
            if args.include_pair_witnesses:
                row['pair_witnesses'] = witnesses
            cliques.append(row)
        note = Path(__file__).with_name('TRACE-H27-CLIQUE-SEPARATION.md')
        result = dict(schema='trace-h27-clique-discovery-v1', assurance=
            'Ordinary conditional H27 rows with exact finite pair checks; saved primal weights are discovery only. No solver, original-model reconstruction, or Lean.',
            receipt=str(args.receipt.resolve()), receipt_sha256=sha(args.receipt),
            separator_source_sha256=sha(__file__), ordinary_note_sha256=sha(note) if note.exists() else None,
            receipt_producer_source_claim=claimed_hash, checked_producer_source_sha256=producer_hash,
            producer_source_match_status='checked' if producer_hash else 'receipt claim only; source file not checked',
            fixed_document=str(args.fixed_members.resolve()) if args.fixed_members else None,
            fixed_document_sha256=sha(args.fixed_members) if args.fixed_members else None,
            kind=receipt.get('kind'), case=receipt.get('case'),
            receipt_premise_sha256=receipt.get('premise_sha256'),
            represented_points=sorted(points(represented)), excluded_points=sorted(points(excluded)),
            fixed_members=fixed, threshold=27, tolerance=rational_record(tolerance),
            literal_premises=[
                'F is a finite simple family of four-sets with no three-member sunflower, including empty core.',
                'Residual members avoid every excluded point; their classes are exact traces on the represented points.',
                'All fixed members lie wholly within represented union excluded points.',
                'H27: every intersecting simple SF4 family has size at most 27.',
            ] + actual_premises,
            search=stats, violated_maximal_cliques_found=len(found),
            clique_rows=cliques, discovery_seconds=time.monotonic()-budget.start,
            deadline_scope='graph construction, clique enumeration, independent pair validation and optional greedy extension; serializing checked results finishes afterward')
        # x mode also guards against a concurrent writer replacing an artifact.
        with args.output.open('x') as stream:
            json.dump(result, stream, indent=2)
            stream.write('\n')
        print(json.dumps(dict(output=str(args.output), source_sha256=result['separator_source_sha256'],
            search=stats, violated_rows=len(cliques),
            largest_discovery_weight=cliques[0]['discovery_weight'] if cliques else None,
            seconds=result['discovery_seconds']), separators=(',', ':')))
    except (ValueError, TypeError, KeyError, BudgetEnd) as e:
        parser.error(str(e))


if __name__ == '__main__':
    main()
