"""Independent literal pattern checks at the cap15 N44-to-N43 interface."""
from itertools import combinations
from collections import Counter
from pathlib import Path
import json

p = [frozenset(map(int, t)) for t in
     "012 015 023 034 045 124 134 135 235 245".split()]
models = 0
for a, b in combinations(p, 2):
    if len(a & b) != 2:
        continue
    f = [t for t in p if t not in (a, b)]
    degrees = Counter(v for t in f for v in t)
    assert all(max(degrees[v] for v in t) == 5 for t in f)
    models += 1
q8 = [frozenset((h,) + e) for h in (0, 1)
      for e in combinations((2, 3, 4), 2)]
q8 += [frozenset((0, 1, v)) for v in (5, 6)]
degrees = Counter(v for t in q8 for v in t)
assert all(max(degrees[v] for v in t) == 5 for t in q8)

r16 = [frozenset(t) for t in combinations(range(4), 3)]
for hubs, triad in [((0, 1), (4, 5, 6)), ((2, 3), (7, 8, 9))]:
    r16 += [frozenset((h,) + e) for h in hubs for e in combinations(triad, 2)]
assert len(set(r16)) == 16
patterns = set()
for removed in r16:
    f = [t for t in r16 if t != removed]
    degrees = Counter(v for t in f for v in t)
    assert min(degrees.values()) >= 3
    for t in f:
        pattern = tuple(sorted(degrees[v] for v in t))
        assert pattern not in ((2, 4, 4), (3, 3, 4))
        patterns.add(pattern)
out = {"P8_intersection_two_deletions": models,
       "P8_member_patterns_checked": models * 8,
       "Q8_member_patterns_checked": len(q8),
       "every_remaining_I8_member_has_degree5_point": True,
       "R16_one_deletions": len(r16),
       "R15_member_patterns_checked": 16 * 15,
       "all_observed_patterns": sorted(patterns),
       "forbidden_patterns_244_334_absent": True,
       "limitation": "Checks literal terminal obstruction, not the upstream geometric derivation or universal rho7 classification."}
Path(__file__).with_name("local-patterns.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
