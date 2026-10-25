"""Alpha round 8: bounded literal controls; no model or checker imports."""
from itertools import combinations
from pathlib import Path
import hashlib
import json

p10 = [frozenset(map(int, t)) for t in
       "012 015 023 034 045 124 134 135 235 245".split()]
shifted = [frozenset(v + 6 for v in t) for t in p10]

def sunflowers(f):
    return [tuple(map(sorted, (a, b, c))) for a, b, c in combinations(f, 3)
            if a & b == a & c == b & c]

# Two proper-trace completions are possible with a complete P10+P9 root.
link = p10 + [t for t in shifted if t != frozenset((6, 7, 8))]
f = [t | {99} for t in link] + [frozenset((0, 6, 7, v)) for v in (100, 101)]
core = set(range(12))
assert len(f) == 21 and len(set(f)) == 21 and not sunflowers(f)
assert [q - {99} for q in f if 99 in q] == link
assert sum(q & core == {0, 6, 7} for q in f if 99 not in q) == 2
third = frozenset((0, 6, 7, 102))
assert sunflowers(f + [third])

# The complete C5 internal cost cannot be dropped.
c5link = [t for t in p10 if 0 in t] + [frozenset((1, 2, 4))] + shifted
g = [t | {99} for t in c5link]
assert len(g) == 16 and len(set(g)) == 16 and not sunflowers(g)
edges = [q - {0, 99} for q in g if {0, 99} <= q]
assert len(edges) == 5 and all(sum(v in e for e in edges) == 2 for v in range(1, 6))
internal = sum(99 in q and q <= {99, 1, 2, 3, 4, 5} for q in g)
assert internal == 1 and sum(99 in q for q in g) - internal == 15

# A3 neighbourhood algebra checked on every coordinate basis.
def neighbours(i):
    return {(i + j) % 8 for j in (3, 4, 5)}
def adjacent(i, j):
    return (j - i) % 8 in (3, 4, 5)
assert all(not adjacent(j, k) for i in range(8)
           for j, k in combinations(neighbours(i), 2))
for j in range(8):
    a = [int(i == j) for i in range(8)]
    b = [sum(a[k] for k in neighbours(i)) for i in range(8)]
    for i in range(8):
        assert b[i] + b[(i + 3) % 8] + b[(i + 5) % 8] == sum(a) + a[i]
w = [0, 15, 13, 0, 12, 0, 15, 13]
wb = [sum(w[k] for k in neighbours(i)) for i in range(8)]
independent = [tuple(i for i in range(8) if mask >> i & 1) for mask in range(256)]
independent = [s for s in independent if all(not adjacent(i, j) for i, j in combinations(s, 2))]
assert max(sum(w[i] for i in s) for s in independent) == 28
assert min(wb[i] for i in range(8) if w[i]) == 25
out = {
    "proper_trace": {"family_size": 21, "tested_member_triples": 1330,
                     "sunflowers": 0, "trace_067_multiplicity": 2,
                     "third_completion_rejected": True},
    "C5_cost": {"family_size": 16, "tested_member_triples": 560,
                "sunflowers": 0, "complete_pair_link": "C5",
                "degree": 16, "internal_count": internal, "degree_minus_internal": 15},
    "A3_positivity": {"basis_identity_checks": 64,
                      "neighbourhoods_independent": True,
                      "deduction": "From sum(b)=3n and b_i<=H: a_i>=2n-5H; no occupied-fibre degree lower bound is used.",
                      "n68_H27_lower_bound": 1, "n68_H28_lower_bound": -4,
                      "cap28_control": {"masses": w, "adjacent_masses": wb,
                                        "minimum_actual_degree": 25, "independence": 28}},
    "limitations": ["The small families test weakened implications, not the size-68 theorem.",
                    "The A3 algebra does not prove Jin or H27.",
                    "No model builder, solver, compiler or broad replay was run."],
}
dest = Path(__file__).with_name("results.json")
dest.write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
