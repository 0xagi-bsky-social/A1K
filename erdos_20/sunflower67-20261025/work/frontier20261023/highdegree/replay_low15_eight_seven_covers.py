#!/usr/bin/env python3
"""Independent deletion-first cover reconstruction for the needed 21 links.

Uses literal sets, the proved Q8 safe-leaf list, and raw cover capacities only.
No producer import, solver, support-first distribution or R15 model is used.
The ordinary arbitrary-support bridge is separately hash-bound below.
"""
import argparse
import hashlib
import itertools
import json
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
PINS = {
    "LOW15_classified_cover_probe.py": "8a0dd2733dafb365a51c26b3512394bb6b7c88399ef5674589e8872ba9c199c3",
    "LOW15-classified-cover-probe.json": "2c13e66d1aa9f8dc1c4319b60c89684b000e571acfa08edc2d33966b14fd271d",
    "LOW15-A3-cover-independent-bridge.md": "43a8e28c18d135437ff97f4012f3d49b7015152a538c2d02b1cb12616968c17b",
    "D16-P8-no-two-cover-exclusion.md": "d2e9688375e99a5a21b2f1bdfaa70ad96dc1ad3ae1ed75695d6bb1c2595eda1d",
    "D17-I7-classification-route.md": "a86e80d8377f24218194461c7e2dd92ffe44c3d6b4a505240bd050f129dcb504",
    "D17-i7-coverage.json": "030fcb5ec6e64c738f306409fca83ed962c3afefb5225378295d3a6601c196df",
}
I7_TEXT = (
    "012 034 134 035 235 145 245",
    "012 034 234 135 235 145 245",
    "012 134 234 135 235 145 245",
    "013 024 134 125 235 045 345",
    "023 124 134 125 235 045 345",
    "014 234 025 125 035 145 345",
    "134 234 125 035 135 045 245",
    "023 024 034 124 134 015 016",
)
SAFE_LEAVES = ((), (), (0,), (), (), (), (0,), (5, 6))


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse(text):
    return tuple(frozenset(int(x) for x in item) for item in text.split())


def key(family):
    return tuple(sorted(tuple(sorted(t)) for t in family))


def sf3(family):
    for a, b, c in itertools.combinations(family, 3):
        if a.intersection(b) == a.intersection(c) == b.intersection(c):
            return False
    return True


def models():
    p8 = parse("023 034 045 124 134 135 235 245")
    for index, template in enumerate(I7_TEXT):
        component = parse(template)
        support = set().union(*component)
        need(len(component) == 7 and sf3(component), "bad literal I7")
        need(all(a & b for a, b in itertools.combinations(component, 2)),
             "I7 is not intersecting")
        # Independently verify the analytical safe-leaf criterion, without
        # testing all Q8 gluings or importing the producer's accepted list.
        safe = tuple(v for v in sorted(support)
                     if all((a - {v}) & (b - {v})
                            for a, b in itertools.combinations(
                                [t for t in component if v in t], 2)))
        need(safe == SAFE_LEAVES[index], "safe-leaf lemma mismatch")
        shifted = tuple(frozenset(v + 6 for v in t) for t in component)
        yield f"P8-i2-H{index}", p8 + shifted

    core = tuple(frozenset((h, a, b)) for h in (0, 1)
                 for a, b in itertools.combinations((2, 3, 4), 2))
    for index, template in enumerate(I7_TEXT):
        component = parse(template)
        shifted = tuple(frozenset(v + 5 for v in t) for t in component)
        fresh = max(set().union(*shifted)) + 1
        # Every allowed subset of the safe vertices is used as the shared
        # leaves; the other leaves are new, distinct points outside K.
        for shared_count in range(3):
            for shared in itertools.combinations(SAFE_LEAVES[index], shared_count):
                leaves = tuple(v + 5 for v in shared) + tuple(
                    fresh + j for j in range(2 - shared_count))
                label = "fresh" if not shared else "shared-" + "-".join(map(str, shared))
                q8 = core + tuple(frozenset((0, 1, v)) for v in leaves)
                yield f"Q8-H{index}-{label}", q8 + shifted


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path,
                        default=HERE / "LOW15-eight-seven-cover-independent-replay.json")
    parser.add_argument("--seconds", type=float, default=10.0)
    args = parser.parse_args()
    need(0 < args.seconds <= 10, "deadline must be in (0,10]")
    started = time.monotonic()
    source_path = Path(__file__).resolve()
    source_hash = sha(source_path)
    dependencies = []
    for name, expected in PINS.items():
        actual = sha(HERE / name)
        need(actual == expected, "dependency changed: " + name)
        dependencies.append({"path": name, "sha256": actual})
    diagnostic = json.loads((HERE / "LOW15-classified-cover-probe.json").read_text())
    need(diagnostic["source_sha256"] == PINS["LOW15_classified_cover_probe.py"],
         "diagnostic producer identity mismatch")
    prior_models = {key(row["link"]): row for row in diagnostic["models"]
                    if row["kind"] in ("P8-i2", "Q8")}
    need(len(prior_models) == 21, "wrong compared model domain")
    all_records, summaries, seen = [], [], set()
    global_max = [0, 0, 0]
    for name, unsorted_link in models():
        need(time.monotonic() - started < args.seconds, "deadline exceeded")
        literal_key = key(unsorted_link)
        need(literal_key not in seen, "duplicate model")
        seen.add(literal_key)
        link = tuple(frozenset(t) for t in literal_key)
        need(len(link) == 15 and len(set(link)) == 15 and sf3(link), "bad link")
        support = set().union(*link)
        need(max(sum(v in t for t in link) for v in support) <= 6,
             "point-degree premise failed")
        candidates3 = tuple(frozenset(t) for t in itertools.combinations(sorted(support), 3))
        candidates4 = tuple(frozenset(t) for t in itertools.combinations(sorted(support), 4))
        maxima = [0, 0, 0]
        counts = [0, 0, 0]
        for d in range(3):
            for deleted in itertools.combinations(range(15), d):
                need(time.monotonic() - started < args.seconds, "deadline exceeded")
                remaining = tuple(t for i, t in enumerate(link) if i not in deleted)
                # Deletion-first literal covering tests, unlike the producer's
                # support-set-first distribution to supersets of missed cones.
                c3 = [c for c in candidates3 if all(c & t for t in remaining)]
                p4 = [c for c in candidates4
                      if all(c & t for t in remaining)
                      and not any(a <= c for a in c3)]
                bound = 2 * len(c3) + len(p4)
                need(bound <= (2, 4, 10)[d], "cover bound failed: " + name)
                maxima[d] = max(maxima[d], bound)
                global_max[d] = max(global_max[d], bound)
                counts[d] += 1
                all_records.append({"model": name, "deleted_indices": deleted,
                                    "C3": key(c3), "P4": key(p4), "raw_bound": bound})
        need(counts == [1, 15, 105], "incomplete deletion domain")
        need(literal_key in prior_models, "independent model absent from producer")
        prior = prior_models[literal_key]
        need(maxima == [prior["bounds"][str(d)]["raw_max"] for d in range(3)],
             "raw maxima disagree with producer")
        summaries.append({"model": name, "producer_model": prior["model"],
                          "link": literal_key, "case_counts": counts,
                          "raw_maxima": maxima})
    need(len(summaries) == 21 and len(all_records) == 2541, "incomplete model domain")
    need(seen == set(prior_models), "independent model coverage differs")
    need(global_max == [2, 4, 10], "unexpected global maxima")
    need(sha(source_path) == source_hash, "source changed during replay")
    for dependency in dependencies:
        need(sha(HERE / dependency["path"]) == dependency["sha256"],
             "dependency changed during replay")
    elapsed = time.monotonic() - started
    need(elapsed <= args.seconds, "deadline exceeded")
    relation_bytes = json.dumps(all_records, sort_keys=True, separators=(",", ":")).encode()
    payload = {
        "status": "PASS", "schema": "low15-eight-seven-deletion-first-v1",
        "source_sha256": source_hash, "dependencies": dependencies,
        "method": "literal sets, deletion-first, analytical safe Q8 leaf domain, raw capacities only",
        "premises": {"complete_link_size": 15, "I7_arbitrary_support_catalogue": True,
                     "P8_i1_excluded_by_bound_dependency": True,
                     "P8_i2_whole_support_isolation": True, "Q8_core_isolation": True,
                     "ambient_support_cutoff": None, "ambient_triple_codegree_cap": 2,
                     "simple_ambient_family": True, "deletion_max": 2},
        "model_count": len(summaries), "case_count": len(all_records),
        "raw_maxima": global_max, "safe_shared_leaf_vertices": SAFE_LEAVES,
        "models": summaries, "cases": all_records,
        "case_relation_sha256": hashlib.sha256(relation_bytes).hexdigest(),
        "seconds": elapsed, "assurance": "independent exact finite reconstruction; ordinary arbitrary-support bridge; not Lean",
    }
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": "PASS", "models": len(summaries),
                      "cases": len(all_records), "raw_maxima": global_max,
                      "seconds": elapsed, "source_sha256": source_hash,
                      "output": str(args.output)}, sort_keys=True))


if __name__ == "__main__":
    main()
