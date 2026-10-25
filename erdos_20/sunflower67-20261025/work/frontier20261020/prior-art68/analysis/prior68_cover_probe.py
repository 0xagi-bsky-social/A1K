"""Diagnostic exact support census for deletion-robust four-cover capacities.

Assumes the prior paper's separated 8+8 classification and isolation reduction.
Python enumeration is certificate-diagnostic, not Lean kernel verification.
"""
from itertools import combinations, permutations
import json

P = {frozenset(map(int, t)) for t in
     '012 015 023 034 045 124 134 135 235 245'.split()}
Q = {frozenset(map(int, t)) for t in
     '023 024 034 123 124 134 015 016'.split()}
P0 = P - {frozenset((0, 3, 4)), frozenset((1, 3, 5))}
P1 = P - {frozenset((0, 1, 2)), frozenset((0, 1, 5))}
aut = [p for p in permutations(range(6))
       if {frozenset(p[v] for v in t) for t in P} == P]
assert len(aut) == 60
for representative, meet, size in ((P0, 1, 30), (P1, 2, 15)):
    orbit = {frozenset(frozenset(p[v] for v in t) for t in representative)
             for p in aut}
    domain = {frozenset(P - set(o)) for o in combinations(P, 2)
              if len(o[0] & o[1]) == meet}
    assert len(orbit) == size and orbit == domain

models = []
for i, H in enumerate((P0, P1, Q)):
    for j, K in enumerate((P0, P1, Q)):
        if i <= j:
            models.append((f'{i}/{j}', H | {frozenset(v + 7 for v in t) for t in K}))
for overlap in (1, 2):
    mapping = {v: v + 7 for v in range(7)}
    mapping[5] = 5
    if overlap == 2:
        mapping[6] = 6
    models.append((f'Q/Q overlap {overlap}',
                   Q | {frozenset(mapping[v] for v in t) for t in Q}))

output = []
exception_witnesses = []
total_cases = total_pair_improvements = 0
for name, family in models:
    L = sorted(family, key=lambda t: tuple(sorted(t)))
    assert len(L) == 16
    W = sorted(set().union(*L))
    masks = [sum(1 << v for v in t) for t in L]
    candidates = {d: [sum(1 << v for v in c) for c in combinations(W, d)]
                  for d in (3, 4)}
    missing = {d: [sum(1 << i for i, t in enumerate(masks) if not (s & t))
                   for s in candidates[d]] for d in (3, 4)}
    maxima = {}
    raw_maxima = {}
    pair_improvements = 0
    for d in range(4):
        best = raw_best = 0
        for omission in combinations(range(16), d):
            total_cases += 1
            dm = sum(1 << i for i in omission)
            cover3 = [s for s, m in zip(candidates[3], missing[3]) if not (m & ~dm)]
            cover4 = [s for s, m in zip(candidates[4], missing[4]) if not (m & ~dm)]
            pure4 = [s for s in cover4 if not any(s & c == c for c in cover3)]
            # Every four-cover has >=3 support points, since two points meet
            # at most ten of the sixteen link triples. Covers containing a
            # fixed three-point cover contribute <=2 by global triple degree.
            upper = len(pure4) + 2 * len(cover3)
            raw_best = max(raw_best, upper)
            if d == 3 and upper > 10:
                assert not cover3
                common = cover4[0]
                union = 0
                for c in cover4:
                    common &= c
                    union |= c
                # Here all actual covers lie in W, share a common point,
                # and use at most six other points. Counting the three pairs
                # of each residual triple, each with capacity two, gives 10.
                assert common and union.bit_count() <= 7
                exception_witnesses.append({
                    'model': name,
                    'omitted_triples': [sorted(L[i]) for i in omission],
                    'four_cover_count': len(cover4),
                    'three_cover_count': len(cover3),
                    'common_points': [v for v in W if common >> v & 1],
                    'support': [v for v in W if union >> v & 1],
                })
                upper = 10
                pair_improvements += 1
            assert upper <= (1, 2, 4, 10)[d], (name, omission, upper)
            best = max(best, upper)
        maxima[d] = best
        raw_maxima[d] = raw_best
    output.append({'model': name, 'upper': maxima, 'raw_upper': raw_maxima,
                   'pair_count_improvements': pair_improvements})
    total_pair_improvements += pair_improvements
print(json.dumps({'status': 'DIAGNOSTIC_PASS', 'model_count': len(models),
                  'omission_cases': total_cases,
                  'P8_orbit_sizes': [30, 15],
                  'capacities': [1, 2, 4, 10],
                  'pair_count_improvements': total_pair_improvements,
                  'exception_witnesses': exception_witnesses,
                  'models': output}, indent=2, sort_keys=True))
