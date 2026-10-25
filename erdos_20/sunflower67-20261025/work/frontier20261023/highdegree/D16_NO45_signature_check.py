#!/usr/bin/env python3
"""Tiny necessary arithmetic census, not a geometric realization search or LP.

Local degree16 signatures come only from the literal P8(two-cover)/Q8
blocks and the explicitly described shared-Q8-leaf correction.
"""
from itertools import combinations, combinations_with_replacement, permutations, product
from collections import Counter
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PAIRS = tuple(combinations(range(4), 2))
PERMS = tuple(permutations(range(4)))
PINDEX = {v: i for i, v in enumerate(PAIRS)}
P10 = [frozenset(map(int, s)) for s in
       '012 015 023 034 045 124 134 135 235 245'.split()]
P8_FAMILIES = [[a for a in P10 if a not in (b, c)]
               for b, c in combinations(P10, 2) if len(b & c) == 2]
Q8 = [frozenset((h,)+p) for h in (0, 1)
      for p in combinations((2, 3, 4), 2)] + [frozenset((0, 1, l)) for l in (5, 6)]


def signatures(family):
    ans = set()
    for anchor in family:
        pairs = []
        for j in sorted(anchor):
            p = sum((b & anchor) == {j} for b in family)
            t = sum((b & anchor) == anchor-{j} for b in family)
            pairs.append((p, t))
        ans.add(tuple(sorted(pairs)))
    return ans


SIG8 = signatures(Q8)
for family in P8_FAMILIES:
    SIG8 |= signatures(family)
SIG7 = {((1, 1), (3, 0), (3, 0))}


def act(p, t, s, perm):
    pp, tt, ss = [0]*6, [0]*4, [0]*4
    for n, (i, j) in enumerate(PAIRS):
        pp[PINDEX[tuple(sorted((perm[i], perm[j])))]] = p[n]
    for i in range(4):
        tt[perm[i]], ss[perm[i]] = t[i], s[i]
    return tuple(pp+tt+ss)


def main():
    p_by_sum = {}
    for p in product(range(4), repeat=6):
        p_by_sum.setdefault(sum(p), []).append(p)
    counts = Counter()
    survivors = {}
    for s in combinations_with_replacement(range(9), 4):
        S = sum(s)
        if S < 28:
            continue
        for t in product(range(2), repeat=4):
            T = sum(t)
            if S < 28+T:
                continue
            for p in p_by_sum.get(44-S-T, ()):
                r = [sum(p[n] for n, e in enumerate(PAIRS) if i in e) for i in range(4)]
                d = [1+s[i]+r[i]+T-t[i] for i in range(4)]
                if max(d) > 16:
                    continue
                counts['base_sorted_singleton_rows'] += 1
                if any(1+p[n]+T-t[i]-t[j] > 6 for n, (i, j) in enumerate(PAIRS)):
                    continue
                if any(s[i] == 8 and r[i] > 6 for i in range(4)):
                    continue
                if any(p[n] == 3 and ((t[i] and s[j] == 8) or (t[j] and s[i] == 8))
                       for n, (i, j) in enumerate(PAIRS)):
                    continue
                if any(t[i] and all(s[j] == 8 for j in range(4) if j != i) and r[i] > 4
                       for i in range(4)):
                    continue
                if min(s) == 8 and min(r) >= 5:
                    continue
                counts['after_elementary_rows'] += 1
                bad = False
                for i in range(4):
                    if d[i] != 16:
                        continue
                    sig = tuple(sorted((p[PINDEX[tuple(sorted((i, j)))]], t[j])
                                       for j in range(4) if j != i))
                    allowed = SIG8 if s[i] == 8 else SIG7 if s[i] == 7 else set()
                    if sig not in allowed:
                        bad = True
                        break
                if bad:
                    continue
                counts['after_degree16_signatures'] += 1
                rep = min(act(p, t, s, q) for q in PERMS)
                survivors[rep] = {'p': list(rep[:6]), 't': list(rep[6:10]),
                                  's': list(rep[10:14])}
    data = {
        'schema': 'cap16-N45-local-signatures-v1',
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'assurance': 'necessary scalar signatures only; not a geometry realization or exclusion certificate',
        'premises': ['global cap16', 'size68', 'N45 actual anchor', 'global noP9/noP10',
                     'R16 absent', 'P8 without two-cover absent', 'B4 and triple-star cuts',
                     'universal degree16 B4 partition and Q8 shared-leaf description'],
        'pair_order': PAIRS, 'triple_index': 'omitted root point',
        'literal_P8_families': len(P8_FAMILIES),
        's8_signatures': sorted(SIG8), 's7_signatures': sorted(SIG7),
        'counts': dict(counts), 'orbit_count': len(survivors),
        'survivors': [survivors[k] for k in sorted(survivors)],
    }
    out = HERE / 'D16-NO45-signature-check.json'
    out.write_text(json.dumps(data, indent=2)+'\n')
    print(json.dumps({'counts': dict(counts), 'orbit_count': len(survivors),
                      'survivors': data['survivors']}, indent=2))


if __name__ == '__main__':
    main()
