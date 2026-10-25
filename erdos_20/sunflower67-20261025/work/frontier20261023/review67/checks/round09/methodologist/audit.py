"""Six exceptional cover cases and fixed-rank arithmetic only; no full census."""
from fractions import Fraction
import itertools as it
import json
import math
from pathlib import Path

BASE = Path(__file__).resolve().parents[3]
HIGH = BASE.parent / "highdegree"


def family(text):
    return {frozenset(map(int, word)) for word in text.split()}


p10 = family("012 015 023 034 045 124 134 135 235 245")
p0 = p10 - family("034 135")
p1 = p10 - family("012 015")
q = family("023 024 034 123 124 134 015 016")
components = [p0, p1, q]
receipt = json.loads((HIGH / "D16-I8-cover-independent-replay.json").read_text())
observations = []
for record in receipt["exception_witnesses"]:
    left, right = map(int, record["model"].split("/"))
    link = components[left] | {frozenset(v + 7 for v in block) for block in components[right]}
    removed = set(map(frozenset, record["omitted_triples"]))
    assert len(link) == 16 and len(removed) == 3 and removed <= link
    remaining = link - removed
    support = sorted(set().union(*link))
    covers = {k: [frozenset(c) for c in it.combinations(support, k)
                  if all(set(c) & block for block in remaining)] for k in (3, 4)}
    assert not covers[3] and len(covers[4]) == 12
    common = set.intersection(*(set(c) for c in covers[4]))
    union = set.union(*(set(c) for c in covers[4]))
    assert sorted(common) == record["common_points"] and sorted(union) == record["support"]
    assert len(common) == 1 and len(union) == 7
    z = next(iter(common))
    triples = [c - {z} for c in covers[4]]
    assert all(len(t) == 3 and len(list(it.combinations(t, 2))) == 3 for t in triples)
    # A family of actual covers has residual pair capacity2 on six points.
    budget = 2 * math.comb(len(union) - 1, 2)
    assert budget == 30 and budget // 3 == 10
    observations.append({"model": record["model"], "deleted": record["omitted_triples"],
                         "three_covers": 0, "four_candidates": 12,
                         "common_point": z, "residual_pair_budget": budget,
                         "actual_cover_upper_bound": budget // 3})

# Audit the parameter substitution in the cited comparison, not theorem validity.
support_bound = 3 * Fraction(863, 432) ** 8
assert math.comb(7, 4) == 35 < 68 <= math.comb(8, 4)
assert support_bound > 760 > 67
assert 600**4 == 129600000000

result = {
    "scope": "Independent literal reconstruction of the six listed raw12 corrections; no full deletion/fibre census or compiler",
    "cover_exceptions": observations,
    "comparison": {"support_size_at_least": 8,
                   "BHL_bound_at_support8_exceeds760": True,
                   "bounded_VC_specialization": 600**4,
                   "maximum67_forces_at68": True},
    "result": "PASS"
}
with Path(__file__).with_name("results.json").open("x") as stream:
    json.dump(result, stream, indent=2)
    stream.write("\n")
print(json.dumps(result, indent=2))
