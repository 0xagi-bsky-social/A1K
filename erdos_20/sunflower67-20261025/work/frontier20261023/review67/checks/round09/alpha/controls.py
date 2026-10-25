"""Bounded independent arithmetic and literal-set checks for Alpha round 9."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import comb
from pathlib import Path
import json

p = tuple(frozenset(map(int, t)) for t in
          "012 015 023 034 045 124 134 135 235 245".split())
y = frozenset(range(6))
z = frozenset(range(6, 12))
link = p + tuple(frozenset(v + 6 for v in t) for t in p[1:])
marker = frozenset((0, 1, 2, 3))
incidence = [(frozenset(t), rhs) for t, rhs in [
    ((6, 7, 8), 2), ((6, 9, 10), 1), ((7, 9, 10), 1),
    ((7, 9, 11), 1), ((8, 9, 11), 1), ((8, 10, 11), 1)]]
exact = [(frozenset(a), frozenset(u), rhs) for a, u, rhs in [
    ((0, 1, 2), (1,), 10), ((0, 4, 5), (0, 5), 3),
    ((2, 3, 5), (2, 5), 3), ((2, 4, 5), (2, 4), 3),
    ((0, 2, 3), (0, 2), 3), ((0, 3, 4), (0, 4), 3),
    ((6, 7, 11), (6, 7, 11), 1), ((6, 8, 9), (6, 8, 9), 1),
    ((7, 8, 10), (7, 8, 10), 1), ((8, 10, 11), (10, 11), 3)]]
assert all(a in link for a, _, _ in exact)
rhs = sum(r for _, r in incidence) + sum(r for _, _, r in exact) + 10
assert rhs == 48
hist = Counter()
excluded = 0
for size in range(5):
    for vs in combinations(range(12), size):
        s = frozenset(vs)
        internal = size == 4 and (s <= y or s <= z)
        if (internal and s != marker) or any(s & t == s & marker == t & marker for t in link):
            excluded += 1
            continue
        q = sum(u <= s for u, _ in incidence)
        q += sum(s & a == u for a, u, _ in exact)
        q += int(3 in s and not (size == 4 and s <= y))
        assert q >= (s != marker)
        if s == marker:
            assert q == 0
        hist[q] += 1
pi = (0, 3, 2, 1, 5, 4)
assert {frozenset(pi[v] for v in t) for t in p} == set(p)
assert frozenset(pi[v] for v in marker) == marker

# All possible nonempty traces in the doubled-P10 isolation argument.
trace_witnesses = []
repetition_required = []
for size in range(1, 5):
    for vs in combinations(range(6), size):
        s = frozenset(vs)
        witnesses = [(a, b) for a, b in product(p, repeat=2) if a & b == a & s == b & s]
        assert witnesses
        a, b = witnesses[0]
        q = s | frozenset(range(100, 104 - size))
        aa, bb = a | {90}, b | {91}
        assert len({aa, bb, q}) == 3 and aa & bb == aa & q == bb & q
        trace_witnesses.append([sorted(s), sorted(a), sorted(b)])
        if not any(a != b for a, b in witnesses):
            repetition_required.append(sorted(s))

bhl = 3 * Fraction(863, 432) ** 8
assert comb(7, 4) == 35 < 68 and bhl > 760
result = {
    "support_parameter_comparison": {"choose_7_4": comb(7, 4), "choose_8_4": comb(8, 4),
                                     "BHL_at_N8": str(bhl), "greater_than_760": True},
    "Ysingle_cover": {"row_count": 17, "rhs": rhs, "admissible": sum(hist.values()),
                      "excluded": excluded, "coefficient_histogram": dict(hist),
                      "stabilizer": pi, "marker_fixed": True,
                      "consequence": "r=49 forces every positive-weight row tight, including d3-6<=10; relabelling forces d1=16."},
    "doubled_P10": {"nonempty_trace_count": len(trace_witnesses),
                    "all_traces_have_literal_sunflower_witness": True,
                    "equal_P10_blocks_required_for_traces": repetition_required,
                    "counting_upper_at_degrees_16_pair3": 27 + 16 + 16 - 3},
    "limits": ["No new literature search: comparison checks the documented retrieved theorem.",
               "The equality check relies on the written row premises and internal assignment.",
               "Doubled-P10 count still imports H27; arbitrary-support transfer is the written trace argument.",
               "No solver, model builder, compiler or broad replay was run."]
}
Path(__file__).with_name("results.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
