#!/usr/bin/env python3
"""Independent literal witness, motif-coverage, and six-subset checker.

Does not import either producer or replay its recursive search. Reconstructs
normalizations by old/new subset sizes, verifies all saved witnesses, then
tests every six-subset using independently precomputed literal conflicts.
"""
from collections import Counter
from itertools import combinations
from pathlib import Path
import hashlib
import json
import time

HERE = Path(__file__).resolve().parent
START = time.monotonic()
COUNTS = Counter()


def require(test, message):
    if not test:
        raise ValueError(message)


def mask(points):
    return sum(1 << x for x in points)


def points(a):
    return [i for i in range(a.bit_length()) if a >> i & 1]


def sf(a, b, c):
    common = a & b
    return a & c == common and b & c == common


def bad(family):
    if any(sf(a, b, c) for a, b, c in combinations(family, 3)):
        return True
    return any(sum((a & b) == 0 for b in family) >= 7 for a in family)


def validate_witness(witness, family):
    require(witness is not None, 'missing rejection witness')
    if witness['kind'] == 'sunflower':
        members = [mask(a) for a in witness['members']]
        require(len(set(members)) == 3 and set(members) <= set(family), 'invalid SF members')
        require(sf(*members), 'false SF witness')
        COUNTS['sunflower_witnesses'] += 1
    elif witness['kind'] in ('rho', 'rho_above_six'):
        anchor = mask(witness['anchor'])
        members = [mask(a) for a in witness.get('disjoint', witness.get('members'))]
        require(anchor in family and len(set(members)) == 7 and set(members) <= set(family),
                'invalid rho members')
        require(all(not (anchor & a) for a in members), 'false rho witness')
        COUNTS['rho_witnesses'] += 1
    else:
        raise ValueError('unknown witness kind')


def normalized_additions(old, size):
    """All old-subsets and exactly one canonical set of fresh labels per size."""
    old = sorted(old)
    fresh = max(old) + 1
    for old_size in range(size + 1):
        for selected in combinations(old, old_size):
            yield tuple(sorted(selected + tuple(range(fresh, fresh + size - old_size))))


def lift(hub, triad):
    return [mask((hub,) + edge) for edge in combinations(triad, 2)]


def receipt(name, source, expected_hash):
    source_hash = hashlib.sha256((HERE / source).read_bytes()).hexdigest()
    require(source_hash == expected_hash, 'producer source changed')
    data = json.loads((HERE / name).read_text())
    require(data['source_sha256'] == source_hash and data['status'] == 'PASS', 'receipt identity/status')
    return data


def check_degree6():
    data = receipt('R15-degree2-degree6-literal.json', 'check_r15_degree2_degree6.py',
                   'a17303505959c6416e16a4400d3f82f848e0f9c5418fe9578c1965fb857ecf60')
    expected = {}
    triad = (4, 5, 6)
    for common in range(4):
        other = tuple(triad[:common]) + tuple(range(7, 10 - common))
        for third in normalized_additions(set(triad) | set(other), 3):
            family = [mask(a) for a in ((0, 1, 2), (0, 1, 3), (1, 2, 3))]
            family += lift(1, triad) + lift(2, other) + lift(3, third)
            expected[(other, third)] = family
    require(len(expected) == 42 + 26 + 15 + 8 == 91, 'degree6 normalization count')
    actual = {(tuple(r['D']), tuple(r['E'])): r for r in data['rows']}
    require(len(actual) == len(data['rows']) and actual.keys() == expected.keys(), 'degree6 motif coverage')
    admitted = 0
    for key, family in expected.items():
        row = actual[key]
        require(row['T'] == list(triad) and len(set(family)) == 12, 'degree6 motif identity')
        if bad(family):
            validate_witness(row['rejection'], family)
            continue
        require(row['rejection'] is None, 'degree6 false rejection')
        admitted += 1
        support = set().union(*(set(points(a)) for a in family))
        fresh = max(support) + 1
        universe = (support - {0, 1, 2, 3}) | set(range(fresh, fresh + 3))
        candidates = {mask(c) for c in combinations(sorted(universe), 3)}
        saved = {mask(w['candidate']): w for w in row['extension_witnesses']}
        require(len(saved) == len(row['extension_witnesses']) and saved.keys() == candidates,
                'degree6 next-triple coverage')
        for candidate, w in saved.items():
            require(not w.get('open'), 'unclosed degree6 candidate')
            pair = [mask(a) for a in w['conflict']]
            require(len(set(pair)) == 2 and set(pair) <= set(family), 'degree6 pair witness identity')
            require(sf(pair[0], pair[1], candidate), 'degree6 false extension witness')
            COUNTS['degree6_next_triple_witnesses'] += 1
    require(admitted == data['valid_partial_motifs'] == 6, 'degree6 admitted count')
    return {'normalized_motifs': len(expected), 'admissible_motifs': admitted,
            'unobstructed_next_triples': 0}


def check_without6():
    data = receipt('R15-degree2-without6-complete.json', 'check_r15_degree2_without6.py',
                   '2a939cdb512e94662443e8db6eb67cc9b43ce22dec9da78ec53dac0384e54905')
    expected = {}
    d = (4, 5, 6)
    for common in range(4):
        e = tuple(d[:common]) + tuple(range(7, 10 - common))
        for uv in normalized_additions({3} | set(d) | set(e), 2):
            family = [mask((0, 1, 2)), mask((1, 2, 3)), mask((0,) + uv)]
            family += lift(1, d) + lift(2, e)
            expected[(e, uv)] = family
    require(len(expected) == 29 + 22 + 16 + 11 == 78, 'without6 normalization count')
    actual = {(tuple(r['E']), tuple(r['uv'])): r for r in data['rows']}
    require(len(actual) == len(data['rows']) and actual.keys() == expected.keys(), 'without6 motif coverage')
    admitted = 0
    budgets = Counter()
    subset_counts = Counter()
    for key, family in expected.items():
        row = actual[key]
        require(row['D'] == list(d) and set(map(mask, row['motif'])) == set(family)
                and len(set(family)) == 9, 'without6 motif identity')
        if bad(family):
            validate_witness(row['rejection'], family)
            continue
        require(row['rejection'] is None, 'without6 false rejection')
        admitted += 1
        support = set().union(*(set(points(a)) for a in family))
        fresh = max(support) + 1
        fresh_set = set(range(fresh, fresh + 3))
        fresh_mask = mask(fresh_set)
        universe = (support - {0, 1, 2}) | fresh_set
        all_candidates = {mask(c) for c in combinations(sorted(universe), 3)}
        allowed = {c for c in all_candidates if not bad(family + [c])}
        require(set(map(mask, row['allowed_next'])) == allowed, 'wrong next-triple domain')
        rejected = {mask(w['candidate']): w['witness'] for w in row['rejected_next']}
        require(rejected.keys() == all_candidates - allowed, 'missing next-triple rejection')
        for c, w in rejected.items():
            validate_witness(w, family + [c])
        outside = [c for c in allowed if c & fresh_mask]
        require(all((c & fresh_mask).bit_count() == 1 for c in outside), 'multiple fresh points allowed')
        pair_types = {c & ~fresh_mask for c in outside}
        capacities = {p: 2 - sum(a & p == p for a in family) for p in pair_types}
        require(all(p.bit_count() == 2 and cap >= 0 for p, cap in capacities.items()), 'invalid core capacity')
        budget = sum(capacities.values())
        require(budget <= 3 and budget == row['whole_completion_exterior_budget'], 'whole-completion budget')
        require({mask(v['pair']): v['capacity'] for v in row['exterior_pairs']} == capacities,
                'incorrect projected pair capacities')
        budgets[budget] += 1
        # Exhaust all six-subsets independently of the producer's recursive tree.
        pool = sorted(allowed)
        bad_pairs = {frozenset((a, b)) for a, b in combinations(pool, 2)
                     if any(sf(a, b, f) for f in family)}
        bad_triples = {frozenset((a, b, c)) for a, b, c in combinations(pool, 3) if sf(a, b, c)}
        for selected in combinations(pool, 6):
            subset_counts['six_subsets_tested'] += 1
            if any(frozenset(pair) in bad_pairs for pair in combinations(selected, 2)):
                subset_counts['literal_pair_conflict'] += 1
            elif any(frozenset(triple) in bad_triples for triple in combinations(selected, 3)):
                subset_counts['literal_triple_conflict'] += 1
            elif any(sum((a & b) == 0 for b in family + list(selected)) >= 7
                     for a in family + list(selected)):
                subset_counts['rho_conflict'] += 1
            else:
                raise ValueError('independent six-subset completion found')
            if time.monotonic() - START > 9:
                raise TimeoutError('independent check exceeded nine seconds')
    require(admitted == data['admissible_partial_motifs'] == 18, 'without6 admitted count')
    return {'normalized_motifs': len(expected), 'admissible_motifs': admitted,
            'whole_completion_budget_histogram': dict(budgets),
            'six_subset_check': dict(subset_counts), 'completions': 0}


def main():
    d6 = check_degree6()
    other = check_without6()
    names = ['check_r15_degree2_degree6.py', 'check_r15_degree2_without6.py',
             'R15-degree2-degree6-literal.json', 'R15-degree2-without6-complete.json',
             'R15-rho6-degree2-support-reduction.md']
    result = {'status': 'PASS', 'schema': 'independent-r15-degree2-support-v1',
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'inputs_sha256': {name: hashlib.sha256((HERE / name).read_bytes()).hexdigest() for name in names},
              'degree2_degree6': d6, 'degree2_without6': other,
              'literal_witness_counts': dict(COUNTS), 'seconds': time.monotonic() - START,
              'assurance': 'Independent exact finite witness/domain reconstruction and six-subset check; ordinary support bridge, not Lean.'}
    (HERE / 'R15-degree2-independent-check.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
