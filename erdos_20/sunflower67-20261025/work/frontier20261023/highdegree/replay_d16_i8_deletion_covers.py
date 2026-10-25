#!/usr/bin/env python3
"""Independent exact deletion-cover reconstruction; no LP or producer import.

Prepared source only. Running this command checks all 8*697=5576 cases.
The proof maps arbitrary ambient four-sets to support triples/four-sets;
it does not restrict unrepresented exterior points.

The reconstruction distributes each support subset to all deletion sets
containing its missed triples. This reverses the old deletion-first loop.
All preconditions and cap inequalities use explicit checks, not assert.
"""
from collections import Counter
from itertools import combinations, permutations
from pathlib import Path
import argparse
import hashlib
import json

HERE = Path(__file__).resolve().parent
OLD = HERE.parents[1] / "frontier20261020/prior-art68/analysis"
PINS = {
    "prior68_cover_probe.py": "13c5468d86b8033cf2ef03811845108f9da7a95d31196590a5cef5bd57c4de37",
    "prior68_cover_probe.json": "66b23589dd87a39a5b2e68d2f71a685b97c46a2fb9f7d992398772916e9bf592",
    "prior68-research.md": "92caa67b0215e80b64b19f25b3d2ba8873f489fb9edc5d389ab3a23d79a9f912",
}
CAPACITIES = (1, 2, 4, 10)
# Explicit triple data, independent of the old producer module.
P10 = frozenset(map(frozenset, (
    (0, 1, 2), (0, 1, 5), (0, 2, 3), (0, 3, 4), (0, 4, 5),
    (1, 2, 4), (1, 3, 4), (1, 3, 5), (2, 3, 5), (2, 4, 5))))


def check(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def canonical_bytes(value):
    return json.dumps(value, separators=(",", ":"), sort_keys=True).encode()


def dependencies():
    records = []
    for name, expected in PINS.items():
        path = OLD / name
        actual = digest(path)
        check(actual == expected, f"Frozen diagnostic dependency changed: {path}")
        records.append({"path": str(path), "sha256": actual})
    return records


def integer_mask(items):
    return sum(1 << i for i in items)


def vertices(mask):
    return [i for i in range(mask.bit_length()) if mask & (1 << i)]


def relabel(family, mapping):
    return frozenset(frozenset(mapping[v] for v in block) for block in family)


def sunflower_free(family):
    return all(not (a & b == a & c == b & c)
               for a, b, c in combinations(family, 3))


def reconstruct_models():
    """Verify both entire P8 omission orbits, then construct eight models."""
    check(len(P10) == 10 and sunflower_free(P10), "Literal P10 is invalid")
    check(all(a & b for a, b in combinations(P10, 2)), "P10 is not intersecting")
    p0 = P10 - {frozenset((0, 3, 4)), frozenset((1, 3, 5))}
    p1 = P10 - {frozenset((0, 1, 2)), frozenset((0, 1, 5))}
    q = frozenset({frozenset((hub, u, v)) for hub in (0, 1)
                   for u, v in combinations((2, 3, 4), 2)}
                  | {frozenset((0, 1, leaf)) for leaf in (5, 6)})
    automorphisms = [perm for perm in permutations(range(6))
                     if relabel(P10, perm) == P10]
    check(len(automorphisms) == 60, "P10 automorphism count is not60")
    orbit_sizes = []
    for representative, overlap, expected in ((p0, 1, 30), (p1, 2, 15)):
        all_omissions = frozenset(P10 - {a, b} for a, b in combinations(P10, 2)
                                 if len(a & b) == overlap)
        image_orbit = frozenset(relabel(representative, perm) for perm in automorphisms)
        check(all_omissions == image_orbit and len(image_orbit) == expected,
              f"P8 omission orbit {overlap} is incomplete")
        orbit_sizes.append(len(image_orbit))
    basic = (p0, p1, q)
    models = []
    for i in range(3):
        for j in range(i, 3):
            shifted = relabel(basic[j], {v: v+7 for v in range(7)})
            models.append((f"{i}/{j}", basic[i], shifted))
    for shared in (1, 2):
        mapping = {v: v+7 for v in range(7)}
        for leaf in (5, 6)[:shared]:
            mapping[leaf] = leaf
        models.append((f"Q/Q overlap {shared}", q, relabel(q, mapping)))
    for name, first, second in models:
        family = first | second
        check(len(first) == len(second) == 8 and not first & second,
              f"Component cardinality failed: {name}")
        check(len(family) == 16 and sunflower_free(family), f"Literal link failed: {name}")
        check(all(a & b for a, b in combinations(first, 2))
              and all(a & b for a, b in combinations(second, 2)),
              f"Component intersection failed: {name}")
        support = set().union(*family)
        check(max(sum(v in block for block in family) for v in support) <= 5,
              f"Two-support-point reduction is invalid: {name}")
    return models, orbit_sizes


def deletion_masks():
    # A separate integer-domain construction gives all 697 deletion sets.
    domain = [mask for mask in range(1 << 16) if mask.bit_count() <= 3]
    check(Counter(mask.bit_count() for mask in domain) == {0: 1, 1: 16, 2: 120, 3: 560},
          "Deletion domain does not have the expected exact coverage")
    return tuple(sorted(domain, key=lambda mask: (mask.bit_count(), mask)))


def distribute_support_covers(link, support, domain):
    """Independent upward-closure construction of all support covers."""
    buckets = {deleted: {3: set(), 4: set()} for deleted in domain}
    all_indices = set(range(16))
    for size in (3, 4):
        for subset in combinations(support, size):
            point_mask = integer_mask(subset)
            missed_indices = {i for i, triple in enumerate(link) if not set(subset) & triple}
            if len(missed_indices) > 3:
                continue
            missed = integer_mask(missed_indices)
            available = sorted(all_indices - missed_indices)
            for extra_count in range(4 - len(missed_indices)):
                for extra in combinations(available, extra_count):
                    deleted = missed | integer_mask(extra)
                    buckets[deleted][size].add(point_mask)
    return buckets


def normalize_exception(record):
    return {"model": record["model"],
            "omitted_triples": sorted(sorted(t) for t in record["omitted_triples"]),
            "four_cover_count": record["four_cover_count"],
            "three_cover_count": record["three_cover_count"],
            "common_points": sorted(record["common_points"]),
            "support": sorted(record["support"])}


def replay():
    before = dependencies()
    legacy = json.loads((OLD / "prior68_cover_probe.json").read_text())
    models, orbit_sizes = reconstruct_models()
    domain = deletion_masks()
    results, exceptions = [], []
    case_digest = hashlib.sha256()
    cases = 0
    for name, first, second in models:
        link = tuple(sorted(first | second, key=lambda block: tuple(sorted(block))))
        support = tuple(sorted(set().union(*link)))
        buckets = distribute_support_covers(link, support, domain)
        upper_max = {str(i): 0 for i in range(4)}
        raw_max = dict(upper_max)
        histogram = Counter()
        improvements = 0
        for deleted in domain:
            size = deleted.bit_count()
            triples = buckets[deleted][3]
            fours = buckets[deleted][4]
            # A support four-set is pure exactly when none of its four
            # constituent triples belongs to the covering triple set.
            pure = {four for four in fours
                    if all(four ^ (1 << v) not in triples for v in vertices(four))}
            raw_upper = len(pure) + 2 * len(triples)
            upper = raw_upper
            witness = None
            if raw_upper > CAPACITIES[size]:
                check(size == 3 and raw_upper == 12 and not triples and len(fours) == 12,
                      f"Unexpected exceptional cover structure: {name}:{deleted}")
                common = integer_mask(support)
                union = 0
                for four in fours:
                    common &= four
                    union |= four
                check(common != 0 and union.bit_count() <= 7,
                      f"No common-point pair-count witness: {name}:{deleted}")
                common_point = vertices(common)[0]
                residual_support = union ^ (1 << common_point)
                pair_capacity = 2 * (residual_support.bit_count()
                                     * (residual_support.bit_count()-1) // 2)
                check(pair_capacity <= 30, "Residual pair-incidence budget exceeds30")
                # Each actual residual triple uses three different pairs;
                # every pair lifts with the common point to a triple of F.
                upper = min(raw_upper, pair_capacity // 3)
                check(upper <= 10, "Pair-incidence correction is insufficient")
                witness = normalize_exception({
                    "model": name,
                    "omitted_triples": [sorted(link[i]) for i in vertices(deleted)],
                    "four_cover_count": len(fours), "three_cover_count": len(triples),
                    "common_points": vertices(common), "support": vertices(union)})
                exceptions.append(witness)
                improvements += 1
            check(upper <= CAPACITIES[size], f"Deletion cap failed: {name}:{deleted}")
            raw_max[str(size)] = max(raw_max[str(size)], raw_upper)
            upper_max[str(size)] = max(upper_max[str(size)], upper)
            histogram[(size, raw_upper, upper)] += 1
            # Commit every exact domain case and complete cover lists, not
            # just the maximum or the exceptional cases.
            case_digest.update(canonical_bytes({
                "model": name, "deleted": deleted, "cover3": sorted(triples),
                "cover4": sorted(fours), "pure4": sorted(pure),
                "raw_upper": raw_upper, "upper": upper, "witness": witness}) + b"\n")
            cases += 1
        results.append({"model": name, "upper": upper_max, "raw_upper": raw_max,
                        "pair_count_improvements": improvements,
                        "omission_cases": len(domain),
                        "histogram": [{"deleted": d, "raw_upper": raw,
                                       "upper": bound, "cases": count}
                                      for (d, raw, bound), count in sorted(histogram.items())]})
    check(cases == 5576 and len(exceptions) == 6, "Full case/exception coverage failed")
    comparable = [{k: row[k] for k in ("model", "upper", "raw_upper", "pair_count_improvements")}
                  for row in results]
    check(comparable == legacy["models"], "Reconstructed maxima differ from frozen diagnostic")
    check(sorted(map(canonical_bytes, exceptions)) == sorted(
          canonical_bytes(normalize_exception(record)) for record in legacy["exception_witnesses"]),
          "Reconstructed exceptions differ from frozen diagnostic")
    check(legacy["model_count"] == 8 and legacy["omission_cases"] == cases
          and legacy["pair_count_improvements"] == len(exceptions)
          and legacy["capacities"] == list(CAPACITIES)
          and legacy["P8_orbit_sizes"] == orbit_sizes,
          "Frozen diagnostic metadata does not match reconstruction")
    check(dependencies() == before, "Dependencies changed during reconstruction")
    return {"schema": "d16-i8-deletion-cover-exact-reconstruction-v1",
            "status": "PASS", "source_sha256": digest(__file__), "dependencies": before,
            "method": "support-first exact upward closure; no producer import or solver",
            "assurance": "Exact Python finite reconstruction, ordinary arbitrary-support bridge; not Lean",
            "premises": {"complete_link_cardinality": 16,
                         "components": "separated I8+I8; P8 full-support isolation; Q8 core isolation",
                         "ambient_uniformity": 4, "ambient_simple": True,
                         "ambient_global_triple_codegree_cap": 2,
                         "ambient_support_cutoff": None, "deletion_size_max": 3},
            "model_count": len(models), "P8_orbit_sizes": orbit_sizes,
            "omission_cases": cases, "capacities": list(CAPACITIES),
            "all_case_cover_lists_sha256": case_digest.hexdigest(),
            "pair_count_improvements": len(exceptions), "exception_witnesses": exceptions,
            "models": results}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = replay()
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": result["status"], "models": result["model_count"],
                      "cases": result["omission_cases"], "capacities": result["capacities"],
                      "corrected_cases": result["pair_count_improvements"],
                      "output": str(args.output)}))


if __name__ == "__main__":
    main()
