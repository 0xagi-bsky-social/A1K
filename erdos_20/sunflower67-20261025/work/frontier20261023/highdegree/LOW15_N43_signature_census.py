#!/usr/bin/env python3
"""Necessary scalar N43 census, retaining the unclassified rho<=6 domain.

No solver. All support normalization is for the complete B4 8+7 link:
the I8 core is isolated and only Q8's two leaves can overlap I7.
"""
from collections import Counter, defaultdict
from itertools import combinations, combinations_with_replacement, permutations, product
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
PAIRS = tuple(combinations(range(4), 2))
PI = {e: i for i, e in enumerate(PAIRS)}
PERMS = tuple(permutations(range(4)))
P10 = tuple(frozenset(map(int, a)) for a in
            '012 015 023 034 045 124 134 135 235 245'.split())
I7_TEXT = (
    '012 034 134 035 235 145 245',
    '012 034 234 135 235 145 245',
    '012 134 234 135 235 145 245',
    '013 024 134 125 235 045 345',
    '023 124 134 125 235 045 345',
    '014 234 025 125 035 145 345',
    '134 234 125 035 135 045 245',
    '023 024 034 124 134 015 016',
)
I7 = tuple(tuple(frozenset(map(int, a)) for a in line.split()) for line in I7_TEXT)


def sunflower_free(family):
    return not any(a & b == a & c == b & c for a, b, c in combinations(family, 3))


def sigs(family):
    for anchor in family:
        s = sum(not (a & anchor) for a in family)
        sig = tuple(sorted((sum(a & anchor == {j} for a in family),
                            sum(a & anchor == anchor - {j} for a in family))
                           for j in anchor))
        yield s, sig


def local_signatures():
    result = defaultdict(set)
    counts = Counter()
    # All literal P8 omissions sharing two points; no orbit-transitivity assumption.
    for b, c in combinations(P10, 2):
        if len(b & c) != 2:
            continue
        h = tuple(a for a in P10 if a not in (b, c))
        for k in I7:
            family = h + tuple(frozenset(v + 10 for v in a) for a in k)
            counts['P8_plus_I7_literal_families'] += 1
            for s, sig in sigs(family):
                result[s].add(sig)
    # Q8 core points 0..4; leaves either meet two distinct I7 points or are fresh.
    core = tuple(frozenset((h,) + e) for h in (0, 1)
                 for e in combinations((2, 3, 4), 2))
    for k0 in I7:
        k = tuple(frozenset(v + 10 for v in a) for a in k0)
        support = sorted(set().union(*k))
        for first in support + [30]:
            for second in support + [31]:
                if first == second:
                    continue
                family = core + (frozenset((0, 1, first)), frozenset((0, 1, second))) + k
                counts['Q8_plus_I7_gluings_tested'] += 1
                if not sunflower_free(family):
                    continue
                counts['Q8_plus_I7_SF_gluings'] += 1
                for s, sig in sigs(family):
                    result[s].add(sig)
    # The exact-rho7 theorem, not a classification of rho<=6 links.
    r16 = tuple(frozenset((h,) + e) for h in (0, 1)
                for e in combinations((4, 5, 6), 2))
    r16 += tuple(frozenset(e) for e in combinations((0, 1, 2, 3), 3))
    r16 += tuple(frozenset((h,) + e) for h in (2, 3)
                 for e in combinations((7, 8, 9), 2))
    for deleted in r16:
        # Complete outer-deletion links are independently excluded by the
        # four actual hub-anchor incidence argument in the named note.
        if not deleted <= {0, 1, 2, 3}:
            continue
        family = tuple(a for a in r16 if a != deleted)
        for s, sig in sigs(family):
            result[s].add(sig)
    return result, counts


def act(p, t, s, q):
    pp, tt, ss = [0] * 6, [0] * 4, [0] * 4
    for n, (i, j) in enumerate(PAIRS):
        pp[PI[tuple(sorted((q[i], q[j])))]] = p[n]
    for i in range(4):
        tt[q[i]], ss[q[i]] = t[i], s[i]
    return tuple(pp + tt + ss)


def common_triangle_obstruction(p, s, r, d, T):
    """Only proved >=3-good-root common-triangle/HP15 implications."""
    good = [i for i in range(4) if s[i] == 8 and r[i] >= 5]
    exceptional = [i for i in range(4) if T == 0 and s[i] == 7 and d[i] == 15]
    nodes = sorted(good + exceptional)
    parent = {i: i for i in nodes}
    def find(i):
        while parent[i] != i:
            i = parent[i]
        return i
    def join(i, j):
        parent[find(i)] = find(j)
    for i, j in combinations(nodes, 2):
        if p[PI[(i, j)]] >= 2:
            join(i, j)
    changed = True
    while changed:
        old = [find(i) for i in nodes]
        for i in good:
            ones = [j for j in good if j != i and p[PI[tuple(sorted((i, j)))]] == 1]
            for j, k in combinations(ones, 2):
                # A good row with two singleton categories has third category3;
                # its two singleton residues are distinct by triple-codegree2.
                if find(j) == find(k):
                    join(i, j)
        changed = old != [find(i) for i in nodes]
    for i in exceptional:
        for j in good:
            if p[PI[tuple(sorted((i, j)))]] == 1 and find(i) == find(j):
                return True
    for i in good:
        group = {j for j in good if find(j) == find(i)}
        if len(group) >= 3:
            for a, b in PAIRS:
                if p[PI[(a, b)]] and len(group - {a, b}) >= 2:
                    return True
    return False


def main():
    signatures, counts = local_signatures()
    p_by_sum = defaultdict(list)
    for p in product(range(4), repeat=6):
        p_by_sum[sum(p)].append(p)
    survivors = {}
    for s in combinations_with_replacement(range(9), 4):
        S = sum(s)
        if S < 28:
            continue
        for t in product(range(2), repeat=4):
            T = sum(t)
            if S < 28 + T:
                continue
            for p in p_by_sum[42 - S - T]:
                r = [sum(p[n] for n, e in enumerate(PAIRS) if i in e) for i in range(4)]
                d = [1 + s[i] + r[i] + T - t[i] for i in range(4)]
                if max(d) > 15:
                    continue
                counts['base_sorted_singleton_rows'] += 1
                if any(1 + p[n] + T - t[i] - t[j] > 6
                       for n, (i, j) in enumerate(PAIRS)):
                    continue
                if any(s[i] == 8 and r[i] > 6 for i in range(4)):
                    continue
                if any(p[n] == 3 and ((t[i] and s[j] == 8) or (t[j] and s[i] == 8))
                       for n, (i, j) in enumerate(PAIRS)):
                    continue
                if any(t[i] and all(s[j] == 8 for j in range(4) if j != i) and r[i] > 4
                       for i in range(4)):
                    continue
                counts['after_elementary_cuts'] += 1
                bad = False
                for i in range(4):
                    if d[i] != 15 or s[i] < 7:
                        continue
                    sig = tuple(sorted((p[PI[tuple(sorted((i, j)))]], t[j])
                                       for j in range(4) if j != i))
                    if sig not in signatures[s[i]]:
                        bad = True
                        break
                if bad:
                    continue
                counts['after_degree15_signatures'] += 1
                if common_triangle_obstruction(p, s, r, d, T):
                    continue
                # Two reciprocal d15/s7/T0 shared-Q8-leaf exceptions give
                # an actual 4-anchor of neighbourhood at most40.
                if T == 0 and any(s[i] == s[j] == 7 and d[i] == d[j] == 15
                                  and p[n] == 1 for n, (i, j) in enumerate(PAIRS)):
                    continue
                counts['after_common_triangle_and_reciprocal_leaf'] += 1
                if T == 0 and min(s) == 8:
                    continue
                if T == 4:
                    continue
                counts['after_closed_all8_T0_and_T4_subcases'] += 1
                if T == 3 and min(s) == 8:
                    continue
                if T == 3:
                    omitted = [i for i in range(4) if t[i]]
                    parent = {i: i for i in omitted}
                    def find(i):
                        while parent[i] != i:
                            i = parent[i]
                        return i
                    for i, j in combinations(omitted, 2):
                        if s[i] == s[j] == 8 and p[PI[(i, j)]] >= 2:
                            parent[find(i)] = find(j)
                    if len({find(i) for i in omitted}) == 1:
                        continue
                counts['after_closed_T3_subcases'] += 1
                rep = min(act(p, t, s, q) for q in PERMS)
                survivors[rep] = {'p': list(rep[:6]), 't': list(rep[6:10]),
                                  's': list(rep[10:14])}
    rows = [survivors[k] for k in sorted(survivors)]
    for row in rows:
        p, t, s = row['p'], row['t'], row['s']
        row['r'] = [sum(p[n] for n, e in enumerate(PAIRS) if i in e) for i in range(4)]
        row['d'] = [1 + s[i] + row['r'][i] + sum(t) - t[i] for i in range(4)]
    data = {
        'schema': 'LOW15-N43-necessary-signatures-v1',
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'assurance': 'Necessary scalar signatures only; no geometric realizability or global exclusion asserted.',
        'unclassified_domain_retained': 'd15 and s<=6 are not filtered by the local signature catalogue',
        'imported_catalogue': 'Eight arbitrary-support I7 types from frozen paper/main.tex:465--529',
        'local_link_basis': ['B4 complete I8+I7', 'P8 type without a two-cover excluded',
                            'Q8 core isolation, only its two leaves may overlap I7',
                            'Exact-rho7 R16-minus-one theorem',
                            'Three good roots with a common triangle and a complementary pair witness',
                            'Reciprocal d15/s7/T0 Q8-leaf exception has an actual N<=40 anchor',
                            'Shared-leaf exception triangle propagates along its two size3 categories',
                            'LOW15-N43-all-eight-no-triples.md',
                            'LOW15-N43-four-triples-exclusion.md',
                            'LOW15-N43-three-triples-all-eight.md',
                            'LOW15-R15-outer-deletion-exclusion.md'],
        'ordinary_dependency_sha256': {
            name: hashlib.sha256((HERE / name).read_bytes()).hexdigest()
            for name in (
                'LOW15-R15-rho7-classification.md',
                'LOW15-R15-outer-deletion-exclusion.md',
                'LOW15-large-singleton-core.md',
                'LOW15-N44-Q8-leaf-R15-reduction.md',
                'LOW15-N43-all-eight-no-triples.md',
                'LOW15-N43-four-triples-exclusion.md',
                'LOW15-N43-three-triples-all-eight.md',
            )
        },
        'pair_order': PAIRS,
        'triple_index': 'omitted root point',
        'degree15_s7_signatures': sorted(signatures[7]),
        'degree15_s8_signatures': sorted(signatures[8]),
        'counts': dict(counts),
        'orbit_count': len(rows),
        'survivors': rows,
    }
    (HERE / 'LOW15-N43-signature-census.json').write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps({'counts': dict(counts), 'orbit_count': len(rows)}, indent=2))


if __name__ == '__main__':
    main()
