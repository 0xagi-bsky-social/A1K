"""Bounded constructive interfaces; no solver, producer import, or full replay."""
from collections import Counter
import itertools as it
import json
from pathlib import Path


def family(words):
    return [frozenset(map(int, word)) for word in words.split()]


def sf(fam):
    return all(not (a & b == a & c == b & c) for a, b, c in it.combinations(fam, 3))


p10 = family("012 015 023 034 045 124 134 135 235 245")
h7 = family("023 024 034 124 134 015 016")
rho_control = [t for t in p10 if t not in family("012 015")] + [frozenset(v + 6 for v in t) for t in h7]
rho = max(sum(not (a & b) for b in rho_control) for a in rho_control)
assert len(rho_control) == 15 and len(set().union(*rho_control)) == 13 and rho == 8 and sf(rho_control)
# The counterexample is admitted by the separately retained rho8 branch; neither
# the rho<=6 support theorem nor the exact-rho7 classification is invoked.
assert not (rho <= 6) and rho != 7

link = p10 + [frozenset(v + 6 for v in t) for t in p10[1:]]
residual = [frozenset((0, 6, 7, 100)), frozenset((0, 6, 7, 101))]
lifted = [t | {99} for t in link] + residual
assert sf(lifted)
core = frozenset(range(12))
refined_core = core | {100}
coarse = Counter(q & core for q in residual)
fine = Counter(q & refined_core for q in residual)
aggregated = Counter()
for trace, count in fine.items():
    aggregated[trace & core] += count
assert aggregated == coarse
assert coarse[frozenset((0, 6, 7))] == 2
assert fine[frozenset((0, 6, 7))] == fine[frozenset((0, 6, 7, 100))] == 1
assert sum(count for trace, count in fine.items() if frozenset((0, 6, 7)) <= trace) == 2

# Every fine trace has exactly one coarse image; old incidence statistics commute
# with summation. This identity does not claim independent equivalence of LPs.
fine_traces = [frozenset(t) for k in range(5) for t in it.combinations(sorted(refined_core), k)]
coarse_traces = {frozenset(t) for k in range(5) for t in it.combinations(sorted(core), k)}
assert {t & core for t in fine_traces} == coarse_traces
row_checks = 0
for k in (1, 2, 3):
    for pts in it.combinations(sorted(core), k):
        incidence = frozenset(pts)
        for trace in fine_traces:
            assert (incidence <= trace) == (incidence <= (trace & core))
            row_checks += 1

# General A3 inverse, with n left symbolic via coefficient vectors.
rows = [[int(j in {(i+3)%8, (i+4)%8, (i+5)%8}) for j in range(8)] for i in range(8)]
for i in range(8):
    assert [rows[i][j] + rows[(i+3)%8][j] + rows[(i+5)%8][j] for j in range(8)] == [1 + int(j == i) for j in range(8)]
assert [sum(row[j] for row in rows) for j in range(8)] == [3]*8
result = {
    "scope": "Guarded theorem domains and counting interfaces only; no numerical model reconstruction",
    "rho_partition": {"size":15, "support":13, "rho":rho, "sunflower_free":True,
                      "branch":"rho=8; excluded from support<=11 and R16-minus-one premises"},
    "trace_refinement": {"coarse_triple_count":2, "refined_proper_count":1,
                         "refined_full_count":1, "incidence_count":2,
                         "fine_trace_domain":len(fine_traces), "coarse_trace_domain":len(coarse_traces),
                         "incidence_identity_checks":row_checks},
    "A3_interface": {"coefficient_identities_verified":True,
                     "derived_bound":"a_i >= 2*n - 5*h from b_i<=h, before using occupied-fibre degree bounds",
                     "n68_h27_lower_bound":136-5*27, "n68_h28_lower_bound":136-5*28},
    "result":"PASS"
}
with Path(__file__).with_name("results.json").open("x") as f:
    json.dump(result, f, indent=2)
    f.write("\n")
print(json.dumps(result, indent=2))
