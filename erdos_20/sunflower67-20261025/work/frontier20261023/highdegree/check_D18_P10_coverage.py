#!/usr/bin/env python3
"""Independent D18 P10+I8 geometry and explicit staged-premise coverage.

Standard library only. Never imports a producer, builds a numerical model, or
runs an LP. A complete conditional marker chain is not a replay of LP arithmetic
or a proof of the imported ordinary family-to-model bridge. Without a manifest,
only geometry and a non-authoritative receipt inventory are checked.
"""
from __future__ import annotations

import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations, permutations, product
import hashlib
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent
KINDS = ('P8-i1', 'P8-i2', 'Q8')
SCHEMA = 'D18-P10-coverage-v1'
ROOT = 15
Y = frozenset(range(6))
# Literal set systems; no producer import or numerical catalogue is used.
P10 = frozenset(frozenset(map(int, word)) for word in
                '012 015 023 034 045 124 134 135 235 245'.split())
Q8 = frozenset(frozenset((h, a, b)) for h in (0, 1)
               for a, b in combinations((2, 3, 4), 2)) | {
                   frozenset((0, 1, 5)), frozenset((0, 1, 6))}
CATEGORIES = ('internal-Z', 'mixed-four-core', 'mixed-three-core-plus-exterior')


def need(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def encode(points):
    return sum(1 << v for v in points)


def decode(number):
    need(type(number) is int and number >= 0, 'Invalid nonnegative integer mask')
    return frozenset(v for v in range(number.bit_length()) if number & (1 << v))


def image(points, permutation):
    return frozenset(permutation[v] for v in points)


def connected_components(family):
    """Components of the triple intersection graph, preserving actual triples."""
    unseen, result = set(family), []
    while unseen:
        component = {min(unseen, key=encode)}
        while True:
            enlarged = component | {t for t in unseen if any(t & u for u in component)}
            if enlarged == component:
                break
            component = enlarged
        unseen -= component
        result.append(frozenset(component))
    return tuple(result)


@lru_cache(None)
def full_automorphisms(family, size):
    # Exhaust all permutations of the literal support, including Q8 leaves.
    return tuple(p for p in permutations(range(size))
                 if frozenset(image(t, p) for t in family) == family)


def point_shape(component, vertex, support):
    edges = frozenset(t - {vertex} for t in component if vertex in t)
    used = frozenset().union(*edges) if edges else frozenset()
    if len(support) != 6 or used != support - {vertex}:
        return None
    reached = {min(used)}
    while True:
        enlarged = reached | set().union(*(e for e in edges if e & reached))
        if enlarged == reached:
            break
        reached = enlarged
    if reached != set(used):
        return None
    degrees = sorted(sum(v in e for e in edges) for v in used)
    if len(edges) == 5 and degrees == [2, 2, 2, 2, 2]:
        return 'C5'
    if len(edges) == 4 and degrees == [1, 1, 2, 2, 2]:
        return 'P5'
    return None


@lru_cache(None)
def deletion_types():
    autos = full_automorphisms(P10, 6)
    need(len(autos) == 60, 'Full P10 automorphism order')
    all_pairs = {frozenset(ab) for ab in combinations(P10, 2)}
    unseen, result = set(all_pairs), {}
    while unseen:
        rep = min(unseen, key=lambda pair: tuple(sorted(map(encode, pair))))
        orbit = {frozenset(image(t, p) for t in rep) for p in autos}
        need(orbit <= unseen, 'Deletion orbit overlaps or leaves domain')
        a, b = tuple(rep)
        name = f'P8-i{len(a & b)}'
        need(name in KINDS[:2] and name not in result, 'Unexpected P8 deletion class')
        result[name] = (rep, orbit, P10 - rep)
        unseen -= orbit
    need(set(result) == set(KINDS[:2]), 'P8 deletion types incomplete')
    need(sum(len(r[1]) for r in result.values()) == 45, 'P8 omitted-pair domain')
    return result


@lru_cache(None)
def reconstruct(kind):
    need(kind in KINDS, 'Unknown link kind')
    rep, deletion_orbit, local_z = (frozenset(), set(), Q8) if kind == 'Q8' else deletion_types()[kind]
    z_size = 7 if kind == 'Q8' else 6
    core_size = 6 + z_size
    z = frozenset(range(6, core_size))
    core = Y | z
    zlink = frozenset(frozenset(v + 6 for v in t) for t in local_z)
    link = P10 | zlink
    components = connected_components(link)
    need(sorted(map(len, components)) == [8, 10], 'Complete link intersection components')
    # Every automorphism preserves the two intersection components: they have
    # distinct sizes. Hence the full group is exactly this direct product.
    ya = full_automorphisms(P10, 6)
    za = full_automorphisms(local_z, z_size)
    group = tuple(a + tuple(v + 6 for v in b) + (core_size,) for a, b in product(ya, za))
    need(len(set(group)) == len(ya) * len(za), 'Product group duplicates')
    for p in group:
        need(frozenset(image(t, p) for t in link) == link, 'Product element changes complete link')
        need(p[core_size] == core_size, 'Exterior marker was not fixed')
    all4 = {frozenset(q) for q in combinations(sorted(core), 4)}
    yi = {q for q in all4 if q <= Y}
    zi = {q for q in all4 if q <= z}
    mixed4 = all4 - yi - zi
    mixed3 = {frozenset(t) | {core_size} for t in combinations(sorted(core), 3)
              if set(t) & Y and set(t) & z}
    domains = {'internal-Z': zi, 'mixed-four-core': mixed4,
               'mixed-three-core-plus-exterior': mixed3}
    records = {'none': dict(marker=None, category='unmarked', orbit_size=0, orbit=[])}
    for prefix, category in zip(('I', 'E4_', 'E3_'), CATEGORIES):
        unseen, covered, counter = set(domains[category]), set(), 0
        while unseen:
            marker = min(unseen, key=encode)
            orbit = {image(marker, p) for p in group}
            need(orbit <= unseen, f'{kind} {category}: orbit overlaps or leaves domain')
            name = f'{prefix}{counter:02d}'
            records[name] = dict(marker=encode(marker), category=category,
                                 orbit_size=len(orbit), orbit=sorted(map(encode, orbit)))
            unseen -= orbit
            covered |= orbit
            counter += 1
        need(covered == domains[category], 'Marker orbit coverage')
    need(sum(len(v) for v in domains.values()) == len(all4 - yi) + len(mixed3),
         'The three marker domains overlap or omit a trace')
    shapes = {str(v): point_shape(P10 if v in Y else zlink, v, Y if v in Y else z)
              for v in sorted(core)}
    metadata = dict(kind=kind, root=ROOT, Y=sorted(Y), Z=sorted(z),
                    exterior_marker=core_size, link=sorted(map(encode, link)),
                    omitted_local_p10_blocks=sorted(map(encode, rep)),
                    p8_deletion_orbit=sorted([sorted(map(encode, pair)) for pair in deletion_orbit]),
                    automorphism_orders=dict(Y=len(ya), Z=len(za), product=len(group)),
                    literal_point_link_shapes=shapes, excluded_Y_internal_count=len(yi), records=records)
    return dict(metadata=metadata, domains=domains, all4=all4, yi=yi, zi=zi,
                core_size=core_size, group=group)


def normalized_metadata(record):
    # Block order is immaterial; orbit IDs/representatives are checked exactly.
    result = dict(record)
    result['link'] = sorted(record['link'])
    return result


def check_metadata(record, kind):
    expected = reconstruct(kind)['metadata']
    need(normalized_metadata(record) == expected, f'{kind}: saved geometry differs from reconstruction')


def read_json(path):
    return json.loads(path.read_text())


def resolve_ref(ref, base):
    need(isinstance(ref, dict) and set(ref) == {'path', 'sha256'}, 'References require path and sha256 only')
    path = Path(ref['path'])
    path = path if path.is_absolute() else base / path
    need(path.is_file(), f'Missing referenced file: {path}')
    need(digest(path) == ref['sha256'], f'Hash mismatch: {path}')
    return path.resolve()


def claimed_strict_bound(receipt):
    """Check recorded scalar arithmetic, not coefficient/model reconstruction."""
    dual = receipt.get('dual')
    if receipt.get('status') != 0 or not isinstance(dual, dict):
        return False
    fields = ('scale', 'H', 'correction', 'upper_numerator')
    need(all(type(dual.get(k)) is int for k in fields), 'Noninteger scalar certificate field')
    need(dual['scale'] > 0, 'Nonpositive dual scale')
    need(dual['H'] + dual['correction'] == dual['upper_numerator'], 'Saved bound arithmetic mismatch')
    zero = receipt.get('certificate_kind') == 'zero-infeasibility'
    flag = 'below0' if zero else 'below50'
    strict = dual['upper_numerator'] < (0 if zero else 50 * dual['scale'])
    if zero:
        need(dual.get('objective') == 'zero', 'Phase-one receipt lacks the zero objective')
        need(receipt.get('original_status') == 2, 'Phase-one original status is not infeasible')
        original_path = Path(receipt['input_receipt_path'])
        need(original_path.is_file() and digest(original_path) == receipt['input_receipt_sha256'],
             'Phase-one original receipt is missing or changed')
        original = read_json(original_path)
        need(original.get('status') == 2 and original.get('premise_sha256') == receipt['premise_sha256']
             and original.get('source_sha256') == receipt['source_sha256'], 'Phase-one input identity mismatch')
        producers = {digest(path) for path in HERE.glob('degree18_p10_phaseone*.py')}
        need(receipt['certificate_producer_sha256'] in producers,
             'No saved phase-one certificate producer matches its hash')
    need(type(dual.get(flag)) is bool and dual[flag] == strict, 'Saved strict-bound flag mismatch')
    for key, countkey, nonnegative in (('ineq', 'upper_rows', True), ('eq', 'equal_rows', False)):
        seen = set()
        for row in dual.get(key, []):
            need(isinstance(row, list) and len(row) == (3 if key == 'ineq' else 2), 'Malformed dual weight')
            index, weight = row[:2]
            need(type(index) is int and 0 <= index < receipt[countkey] and index not in seen,
                 'Invalid or repeated dual row index')
            need(type(weight) is int and (not nonnegative or weight >= 0), 'Invalid dual weight sign/type')
            seen.add(index)
    return strict


def check_receipt(receipt, source_hashes):
    kind, case = receipt['kind'], receipt['case']
    g = reconstruct(kind)
    need(case in g['metadata']['records'], 'Unknown receipt case')
    check_metadata(receipt['geometry'], kind)
    need((receipt['target_residuals'], receipt['point_cap'], receipt['mu']) == (50, 18, 41),
         'Wrong numerical branch guards')
    need(receipt['source_sha256'] in source_hashes, 'No saved producer source matches this receipt hash')
    for key in ('empty_z', 'forbid_four_core', 'degree_distributions', 'crowding_imports'):
        need(type(receipt[key]) is bool, f'Invalid flag {key}')
    forbidden = receipt['forbidden']
    need(isinstance(forbidden, list) and len(set(forbidden)) == len(forbidden), 'Repeated forbidden trace')
    for value in forbidden:
        decode(value)
    configs = [p for p in receipt['literal_premises'] if isinstance(p, dict)]
    expected = {key: receipt[key] for key in ('case', 'empty_z', 'assigned_z', 'forbidden',
                                            'forbid_four_core', 'degree_distributions', 'crowding_imports')}
    expected['actual_marker'] = g['metadata']['records'][case]['marker']
    need(configs == [expected], 'Literal branch premise differs from receipt header')
    identity = {key: receipt[key] for key in ('source_sha256', 'imported_local43_sha256',
                                             'structural_note_sha256', 'pool_note_sha256', 'kind', 'literal_premises')}
    identity['imported_crowding_sources'] = receipt.get('imported_crowding_sources', {})
    need(canonical_digest(identity) == receipt['premise_sha256'], 'Premise fingerprint mismatch')
    return claimed_strict_bound(receipt)


def tokens_for_case(kind, case):
    g = reconstruct(kind)
    r = g['metadata']['records'][case]
    if case == 'none':
        return set()
    if r['category'] == 'mixed-three-core-plus-exterior':
        return {('mixed3', value ^ (1 << g['core_size'])) for value in r['orbit']}
    return {('core4', value) for value in r['orbit']}


def required_tokens(kind):
    result = set()
    for case in reconstruct(kind)['metadata']['records']:
        result |= tokens_for_case(kind, case)
    return result


def forbidden_token(value, kind, marker):
    g = reconstruct(kind)
    points = decode(value)
    c = g['core_size']
    if len(points) == 4 and all(v < c for v in points):
        return ('core4', value)
    core = points - {c}
    if (len(core) == 3 and all(v < c for v in core) and core & Y and core - Y
            and (points == core or (points == core | {c} and marker is not None and marker >> c))):
        return ('mixed3', encode(core))
    raise ValueError(f'Unsupported forbidden trace {value}: no prior marker theorem covers it')


def reconstruct_patterns(kind, remaining_cases):
    """All literal SF-compatible complete assignments on an allowed orbit union."""
    g = reconstruct(kind)
    records = g['metadata']['records']
    need(isinstance(remaining_cases, list) and remaining_cases
         and len(set(remaining_cases)) == len(remaining_cases), 'Invalid remaining-internal cases')
    allowed = set()
    for case in remaining_cases:
        need(case in records and records[case]['category'] == 'internal-Z', 'Pattern case is not internal')
        allowed |= set(records[case]['orbit'])
    allowed = sorted(allowed)
    need(len(allowed) <= 8, 'Pattern checker is bounded to at most eight internal candidates')
    fixed = [decode(t) | {ROOT} for t in g['metadata']['link']]
    compatible = set()
    for size in range(len(allowed) + 1):
        for chosen in combinations(allowed, size):
            family = fixed + [decode(t) for t in chosen]
            if not any(a & b == a & c == b & c for a,b,c in combinations(family, 3)):
                compatible.add(chosen)
    # All relevant group elements are reconstructed from the literal full link.
    # Remove repeats which have identical action on the candidate internal sets.
    actions = {tuple(encode(image(decode(t), q)) for t in allowed) for q in g['group']}
    maps = [dict(zip(allowed, action)) for action in actions]
    seen, result = set(), []
    for representative in sorted(compatible, key=lambda row: (len(row), row)):
        if representative in seen:
            continue
        orbit = {tuple(sorted(pm[t] for t in representative)) for pm in maps}
        need(orbit <= compatible and not orbit & seen, 'Invalid literal pattern orbit')
        seen |= orbit
        result.append(dict(id=len(result), representative=list(representative),
                           orbit_size=len(orbit), orbit=[list(row) for row in sorted(orbit)]))
    need(seen == compatible, 'Pattern orbit domain incomplete')
    return dict(all_labelled_patterns=len(compatible), records=result)


def check_pattern_plan(path, kind, remaining_cases):
    expected = reconstruct_patterns(kind, remaining_cases)
    need(read_json(path) == expected, 'Saved complete-internal pattern plan differs from literal reconstruction')
    return expected


def check_chain(manifest, base, source_hashes):
    need(set(manifest) == {'schema', 'base_premises', 'stages'}, 'Manifest fields/schema')
    need(manifest['schema'] == SCHEMA, 'Unknown manifest schema')
    premises = manifest['base_premises']
    need(set(premises) == {'Y-internals-absent'}, 'Explicit Y-internals-absent bridge reference required')
    bridge = resolve_ref(premises['Y-internals-absent'], base)
    stages, all_closed, stage_outputs = {}, {kind: set() for kind in KINDS}, []
    directly_closed = set()
    for stage in manifest['stages']:
        normal_fields = {'id', 'kind', 'depends_on', 'receipts'}
        pattern_fields = {'pattern_plan', 'remaining_internal_cases'}
        pattern_stage = bool(set(stage) & pattern_fields)
        need(set(stage) == normal_fields | (pattern_fields if pattern_stage else set()), 'Stage fields')
        ident, kind = stage['id'], stage['kind']
        need(isinstance(ident, str) and ident and ident not in stages and kind in KINDS, 'Invalid stage identity')
        dependencies = stage['depends_on']
        need(isinstance(dependencies, list) and len(set(dependencies)) == len(dependencies), 'Duplicate dependency')
        prior = {('core4', encode(q)) for q in reconstruct(kind)['yi']}
        ancestors = set()
        for dep in dependencies:
            need(dep in stages and stages[dep]['kind'] == kind, 'Missing, future, or wrong-kind dependency')
            prior |= stages[dep]['available']
            ancestors |= {dep} | stages[dep]['ancestors']
        pattern_by_rep, pattern_plan = {}, None
        if pattern_stage:
            plan_path = resolve_ref(stage['pattern_plan'], base)
            pattern_plan = check_pattern_plan(plan_path, kind, stage['remaining_internal_cases'])
            allowed = {('core4', value) for case in stage['remaining_internal_cases']
                       for value in reconstruct(kind)['metadata']['records'][case]['orbit']}
            remaining = {('core4', encode(q)) for q in reconstruct(kind)['zi']} - prior
            need(allowed == remaining, 'Pattern domain is not exactly the internals remaining after dependencies')
            pattern_by_rep = {tuple(row['representative']): row['id'] for row in pattern_plan['records']
                              if row['representative']}
        # All siblings use only previously completed dependencies. No circular
        # exclusion among receipts in the same stage is permitted.
        newly_closed, selected, seen_cases, closed_patterns = set(), [], set(), set()
        direct = False
        need(isinstance(stage['receipts'], list) and stage['receipts'], 'Empty active stage')
        for ref in stage['receipts']:
            path = resolve_ref(ref, base)
            receipt = read_json(path)
            need(receipt['kind'] == kind, 'Receipt kind differs from stage')
            need(check_receipt(receipt, source_hashes), f'Active receipt has no strict recorded bound: {path.name}')
            case = receipt['case']
            if pattern_stage:
                need(case == 'none' and isinstance(receipt['assigned_z'], list), 'Pattern receipt must give a complete assigned_z with case none')
                representative = tuple(receipt['assigned_z'])
                need(representative in pattern_by_rep, 'Receipt does not select a nonempty canonical complete pattern')
                pattern_id = pattern_by_rep[representative]
                key = pattern_id
            else:
                need(receipt['assigned_z'] in (None, []), 'Nonempty assigned-Z branches require an explicit pattern stage')
                key = case
            need(key not in seen_cases, 'Duplicate case or pattern within a stage')
            seen_cases.add(key)
            g = reconstruct(kind)
            marker = g['metadata']['records'][case]['marker']
            required = set()
            if receipt['empty_z'] or receipt['assigned_z'] == []:
                required |= {('core4', encode(q)) for q in g['zi']}
            if receipt['forbid_four_core']:
                required |= {('core4', encode(q)) for q in g['all4']}
            required |= {forbidden_token(value, kind, marker) for value in receipt['forbidden']}
            need(required <= prior, f'{ident}/{case}: {len(required-prior)} forbidden premises are unproved by explicit dependencies')
            conclusion = set() if pattern_stage else tokens_for_case(kind, case)
            need(case == 'none' or not conclusion & prior, 'Active marker already excluded by its own premises')
            newly_closed |= conclusion
            if pattern_stage:
                closed_patterns.add(pattern_id)
            elif case == 'none':
                direct = True
                newly_closed |= required_tokens(kind)
            selected.append(dict(path=str(path), sha256=digest(path), case=case,
                                 required_exclusions=len(required), orbit_size=len(conclusion),
                                 certificate_kind=receipt.get('certificate_kind', 'residual-upper-bound'),
                                 claimed_upper_numerator=receipt['dual']['upper_numerator'],
                                 scale=receipt['dual']['scale'], source_sha256=receipt['source_sha256']))
            if pattern_stage:
                selected[-1].update(pattern_id=pattern_id, assigned_z=receipt['assigned_z'])
        pattern_summary = None
        if pattern_stage:
            missing_patterns = sorted(set(pattern_by_rep.values()) - closed_patterns)
            if not missing_patterns:
                newly_closed |= remaining
            pattern_summary = dict(plan_sha256=digest(plan_path),
                                   all_labelled_patterns=pattern_plan['all_labelled_patterns'],
                                   nonempty_orbits=len(pattern_by_rep),
                                   closed_pattern_ids=sorted(closed_patterns),
                                   missing_pattern_ids=missing_patterns,
                                   remaining_internals_concluded_absent=not missing_patterns)
        stages[ident] = dict(kind=kind, available=prior | newly_closed, ancestors=ancestors)
        all_closed[kind] |= newly_closed
        if direct:
            directly_closed.add(kind)
        stage_outputs.append(dict(id=ident, kind=kind, depends_on=dependencies,
                                  newly_closed_traces=len(newly_closed), receipts=selected,
                                  pattern_coverage=pattern_summary))
    coverage = {}
    for kind in KINDS:
        records = reconstruct(kind)['metadata']['records']
        missing = [case for case in records if case != 'none'
                   and not tokens_for_case(kind, case) <= all_closed[kind]]
        coverage[kind] = dict(complete=not missing, direct_unmarked_contradiction=kind in directly_closed,
                              covered_orbits=len(records)-1-len(missing), total_orbits=len(records)-1,
                              missing_cases=missing)
    return dict(complete_conditional_marker_chain=all(v['complete'] for v in coverage.values()),
                base_bridge=dict(path=str(bridge), sha256=digest(bridge)),
                coverage=coverage, stages=stage_outputs)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--directory', type=Path, default=HERE/'degree18_p10')
    ap.add_argument('--manifest', type=Path, help='Explicit active-chain manifest; relative refs use its directory')
    ap.add_argument('--output', type=Path, default=HERE/'D18-P10-coverage-diagnostic.json')
    ap.add_argument('--require-complete', action='store_true', help='Fail unless the explicit chain covers all three kinds')
    ap.add_argument('--require-kinds', nargs='+', choices=KINDS, default=[], help='Require these explicitly named kinds, while leaving others open')
    args = ap.parse_args()
    start = time.monotonic()
    sources = {digest(p): str(p) for p in HERE.glob('degree18_p10_projection*.py')}
    summaries = {}
    for kind in KINDS:
        path = args.directory/f'{kind}-catalogue.json'
        saved = read_json(path)
        check_metadata(saved, kind)
        g = reconstruct(kind)
        summaries[kind] = dict(catalogue_sha256=digest(path),
                               automorphism_orders=g['metadata']['automorphism_orders'],
                               deletion_orbit_size=len(g['metadata']['p8_deletion_orbit']),
                               domain_sizes={k: len(v) for k,v in g['domains'].items()},
                               orbit_counts=dict(Counter(r['category'] for r in g['metadata']['records'].values())),
                               reconstructed_geometry_sha256=canonical_digest(g['metadata']))
    pattern_checks = {}
    pattern_path = args.directory/'q8-I06-pattern-plan.json'
    if pattern_path.exists():
        checked = check_pattern_plan(pattern_path, 'Q8', ['I06'])
        pattern_checks['Q8-I06'] = dict(plan_sha256=digest(pattern_path),
                                        all_labelled_patterns=checked['all_labelled_patterns'],
                                        orbit_sizes=[r['orbit_size'] for r in checked['records']],
                                        nonempty_orbits=sum(bool(r['representative']) for r in checked['records']))
    inventory, invalid = [], []
    for path in sorted(args.directory.glob('*.json')):
        try:
            rec = read_json(path)
            if not isinstance(rec, dict) or not {'kind','case','source_sha256','premise_sha256'} <= rec.keys():
                continue
            strict = check_receipt(rec, sources)
            inventory.append(dict(path=path.name, sha256=digest(path), kind=rec['kind'], case=rec['case'],
                                  strict_recorded_bound=strict, source_sha256=rec['source_sha256'],
                                  empty_z=rec['empty_z'], forbidden_count=len(rec['forbidden']),
                                  forbid_four_core=rec['forbid_four_core']))
        except (ValueError, KeyError, TypeError) as error:
            invalid.append(dict(path=path.name, error=str(error)))
    chain = None
    if args.manifest:
        chain = check_chain(read_json(args.manifest), args.manifest.resolve().parent, sources)
    result = dict(result='GEOMETRY_PASS' if chain is None else
                  ('COMPLETE_CONDITIONAL_MARKER_CHAIN' if chain['complete_conditional_marker_chain'] else 'PARTIAL_CONDITIONAL_MARKER_CHAIN'),
                  scope='Independent literal geometry and stage-premise coverage; recorded scalar bound checks only. No LP coefficient replay, imported-lemma validation, terminal proof, or Lean proof.',
                  geometry=summaries, pattern_plan_checks=pattern_checks,
                  receipt_inventory=inventory, invalid_inventory_files=invalid,
                  active_chain=chain, manifest_sha256=digest(args.manifest) if args.manifest else None,
                  checker_sha256=digest(Path(__file__)), seconds=time.monotonic()-start)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('receipt_inventory','active_chain')}, indent=2))
    if chain:
        print(json.dumps(dict(active_chain_coverage=chain['coverage']), indent=2))
    print(json.dumps(dict(receipt_inventory_count=len(inventory), invalid_inventory_count=len(invalid), output=str(args.output))))
    if args.require_complete:
        need(chain is not None and chain['complete_conditional_marker_chain'], 'Explicit complete conditional marker chain is not available')
    for kind in args.require_kinds:
        need(chain is not None and chain['coverage'][kind]['complete'], f'Explicit complete {kind} marker chain is not available')


if __name__ == '__main__':
    main()
