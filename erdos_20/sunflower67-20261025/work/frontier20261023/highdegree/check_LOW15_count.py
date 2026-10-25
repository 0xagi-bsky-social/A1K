#!/usr/bin/env python3
"""Small independent integer/trace check for the LOW15 cone average.

Standard library only: no numerical model, LP, or Lean import. Mathematical
family-to-scalar implications and the external H27/cross15 facts remain
ordinary premises, documented in LOW15-count-check.md.
"""
from itertools import combinations, combinations_with_replacement
import hashlib
import json
from pathlib import Path


def require(value, message):
    if not value:
        raise ValueError(message)


P10 = frozenset(frozenset(map(int, t)) for t in
                '012 015 023 034 045 124 134 135 235 245'.split())
Y = frozenset(range(6))
deleted = frozenset((0, 1, 2))
opposite = Y - deleted
P9 = P10 - {deleted}
pair_caps = (10, 10, 8, 5, 4, 2, 1)
allowed = tuple((h, b) for h in range(11) for b in range(7)
                if h <= pair_caps[b] and h + b <= 10)
max_b = {h: max(b for hh, b in allowed if hh == h) for h in range(11)}

# Every constraint involving different coordinates depends on h alone. For
# fixed h, the objective increases with b, so choosing max_b loses no optimum.
# The remaining constraints and objective are symmetric in all six vertices;
# nondecreasing h vectors cover every labelled possibility up to permutation.
checked = 0
best = -1
maximizers = []
best_without_cross15 = -1
for hs in combinations_with_replacement(range(11), 6):
    if sum(hs) > 27:
        continue
    bs = tuple(max_b[h] for h in hs)
    score = 5 * sum(hs) + 2 * sum(bs)
    best_without_cross15 = max(best_without_cross15, score)
    if hs[-1] + hs[-2] > 15:
        continue
    checked += 1
    if score > best:
        best = score
        maximizers = [(hs, bs)]
    elif score == best:
        maximizers.append((hs, bs))
require(best == 179, 'Six-coordinate scalar maximum changed')
require(best_without_cross15 == 183, 'Cross15 sensitivity check changed')

# Check the EXACT contribution identities separately on every possible trace.
# This includes every internal four-set, without sunflower filtering.
checked_traces = 0
for size in range(5):
    for points in combinations(Y, size):
        U = frozenset(points)
        w10 = sum(bool(U & T) for T in P10)
        rhs10 = (10 * size + 5 * (size == 1) + 4 * (size == 2)
                 - 3 * (size == 3 and U not in P10) - 10 * (size == 4))
        require(3 * w10 == rhs10, f'P10 count failure at {sorted(U)}')
        w9 = sum(bool(U & T) for T in P9)
        pure_deleted_single = size == 1 and U <= deleted
        pure_opposite_single = size == 1 and U <= opposite
        nontransversal = size == 3 and not all(U & T for T in P9)
        rhs9 = (9 * size + 3 * pure_deleted_single + 6 * pure_opposite_single
                + 3 * (size == 2) + 3 * (size == 2 and U <= opposite)
                - 3 * nontransversal - 9 * (size == 4))
        require(3 * w9 == rhs9, f'P9 count failure at {sorted(U)}')
        checked_traces += 1
require(checked_traces == 57, 'Incomplete trace domain')

print(json.dumps({
    'result': 'PASS',
    'scope': 'Exact finite scalar maximum and literal cone-count identities; no geometric-premise proof or LP/Lean replay.',
    'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'allowed_h_b_pairs': len(allowed),
    'max_b_by_h': max_b,
    'feasible_sorted_h_vectors': checked,
    'scalar_maximum': best,
    'scalar_maximum_without_cross15': best_without_cross15,
    'maximizer_count': len(maximizers),
    'one_maximizer': {'h': maximizers[-1][0], 'b': maximizers[-1][1]},
    'traces_checked_per_component': checked_traces,
    'P10_low15_lower_3W': 3 * 10 * (41 - 15),
    'P10_low15_upper_3W': 10 * 6 * (15 - 5) + best,
    'P9_cap14_lower_2W': 2 * 9 * (41 - 14),
    'P9_cap14_upper_2W': 45 * 14 - 155,
    'P9_cap15_minimum_root_degree': next(
        m for m in range(16) if 2 * 9 * (41 - m) <= 45 * 15 - 155),
}, indent=2))
