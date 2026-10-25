"""Fresh bounded final-audit controls, with no proof-package imports."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product
from pathlib import Path
import json

# SF2: no three-edge star and no three-edge matching imply maximum degree 2
# and total matching number at most 2. Components are paths or cycles.
types = [(f"P{v}", v - 1, v // 2, v - 2) for v in range(2, 6)]
types += [(f"C{v}", v, v // 2, v) for v in range(3, 6)]
root_types = {5: [], 6: []}
max_cost = {}
for count in (1, 2):
    for components in combinations_with_replacement(types, count):
        if sum(c[2] for c in components) > 2:
            continue
        degree = sum(c[1] for c in components)
        partners = sum(c[3] for c in components)
        cost = Fraction(degree * (degree - 1) - partners, 2)
        max_cost[degree] = max(max_cost.get(degree, 0), cost)
        if degree in root_types:
            root_types[degree].append([c[0] for c in components])
assert max_cost == {1: 0, 2: 1, 3: Fraction(5, 2), 4: 5, 5: 8, 6: 12}
assert root_types == {5: [["C5"], ["P3", "C3"]], 6: [["C3", "C3"]]}
assert all(max_cost[d] <= Fraction(19*d, 6) - 7 for d in range(3, 7))
assert (Fraction(285, 2) - 60) // 7 == 11

# D17 P10: literal meeting coefficients and every nonnegative count tuple.
p = [frozenset(map(int, t)) for t in "012 015 023 034 045 124 134 135 235 245".split()]
meet = {k: sorted(set(sum(bool(set(vs) & t) for t in p)
                    for vs in combinations(range(6), k))) for k in (1, 2, 3)}
assert meet == {1: [5], 2: [8], 3: [9, 10]}
assert all(any(not (set(vs) & t) for t in p) for vs in combinations(range(6), 2))
best = -1
maximizers = []
admitted = 0
for pairs in range(19):
    for triples in range(21):
        for singletons in range(52 - pairs - triples):
            empty = 51 - pairs - triples - singletons
            if pairs + triples < 24 or singletons + 2*pairs + 3*triples > 60:
                continue
            admitted += 1
            bound = 5*singletons + 8*pairs + 10*triples
            if bound > best:
                best, maximizers = bound, []
            if bound == best:
                maximizers.append([empty, singletons, pairs, triples])
assert best == 234 < 10*(41 - 17) == 240

# A3: exhaust all small mass profiles and all star image supports.
adj = [{(i+j) % 8 for j in (3, 4, 5)} for i in range(8)]
profiles = list(r for r in product(range(3), repeat=8) if sum(r) == 4)
independent_masks = []
nonindependent_masks = []
for bits in range(1, 256):
    s = tuple(i for i in range(8) if bits >> i & 1)
    neighbours = {i: adj[i].intersection(s) for i in s}
    edges = sum(map(len, neighbours.values())) // 2
    if not edges:
        windows = [i for i in range(8) if set(s) <= {(i+j) % 8 for j in range(3)}]
        assert windows
        independent_masks.append((s, windows))
    elif edges <= 2:  # With weights at least1, more edges violate sum q<=4.
        joined = tuple(i for i in s if neighbours[i])
        isolated = tuple(i for i in s if not neighbours[i])
        nonindependent_masks.append((s, neighbours, joined, isolated))
feasible_summaries = 0
for r in profiles:
    a = [7 + r[i] + r[(i+3) % 8] + r[(i+5) % 8] for i in range(8)]
    assert sum(a) == 68
    assert [sum(a[j] for j in adj[i]) for i in range(8)] == [25 + v for v in r]
    for s, windows in independent_masks:
        assert all(sum(a[(i+j) % 8] for j in range(3)) - 15 >= 10 for i in windows)
    for s, neighbours, joined, isolated in nonindependent_masks:
        # Every joined weight is at most2 from its neighbour's q<=r<=2.
        for values in product((1, 2), repeat=len(joined)):
            t = dict(zip(joined, values))
            if any(sum(t[j] for j in neighbours[i]) > r[i] for i in joined):
                continue
            remaining = 15 - sum(values)
            if not len(isolated) <= remaining <= sum(a[i] for i in isolated):
                continue
            feasible_summaries += 1
            starts = [i for i in range(8) if set(s) == {(i+j) % 8 for j in range(4)}]
            assert starts and len(joined) == len(isolated) == 2
            k = starts[0]
            u, v = k, (k+3) % 8
            assert set(joined) == {u, v}
            assert all(remaining - a[j] >= 4 for j in isolated)
            # Each three-index window supplies actual nonstar covers after
            # deleting the opposite endpoint's actual cones.
            assert sum(a[(k+j) % 8] for j in range(3)) - (15-t[v]) >= 10+t[v]
            assert sum(a[(k+j) % 8] for j in range(1, 4)) - (15-t[u]) >= 10+t[u]

out = {
    "SF2_complete_links": {"max_intersection_cost": {str(k): str(v) for k, v in max_cost.items()},
                           "root_types": root_types, "derived_support_cap": 11},
    "D17_P10": {"meeting_coefficients": meet, "admitted_scalar_tuples": admitted,
                "maximum": best, "maximizers_OHPE": maximizers, "required": 240},
    "A3_star": {"mass_profiles": len(profiles), "independent_supports": len(independent_masks),
                "feasible_nonindependent_support_weight_summaries": feasible_summaries,
                "all_have_four_consecutive_support": True,
                "endpoint_weights": [1, 2], "interior_weights_at_least": 4,
                "actual_cover_lower_bounds": [10, 11, 12]},
    "limits": ["SF2 component classification is conditional on the elementary maximum-degree/matching characterization.",
               "D17 check verifies the scalar contradiction after the written C5, pair-pool and H27 premises.",
               "A3 check verifies the star-support and cover-count interface after a homomorphism with the stated masses exists.",
               "No model builder, solver, external source search, compiler or large replay was run."]
}
Path(__file__).with_name("interfaces.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
