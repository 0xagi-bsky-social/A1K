#!/usr/bin/env python3
"""Append completed E3 siblings to the exact existing70-node Q8 E4 plan.

Metadata only: no model, solver, replay, or catalogue import. The generic
stage checker must subsequently validate every named exact replay and orbit.
No initial E4 node is regenerated, reordered, or assigned new ancestry.
"""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUT = HERE / "degree17_full"
V9 = "31368d8392328daa9f161b23e40ef7c3df3d9acd4743cf4914f9df0215b74eb2"
PHASE = "a38b7f30dbdcc54f2452d540f019bcb22f2823fd61c2d8925180c36ca00c6f70"
E4_PLAN_SHA = "a57524270adb7b3e983f118ab050902fcc683057dd1b058df273a95da5c7347b"


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def strict(d):
    q = d.get("dual", {})
    zero = d.get("certificate_kind") == "zero-infeasibility"
    vals = [q.get(k) for k in ("scale", "H", "correction", "upper_numerator")]
    return (d.get("status") == 0 and all(type(v) is int for v in vals)
            and vals[0] > 0 and vals[3] == vals[1] + vals[2]
            and vals[3] < (0 if zero else 51 * vals[0])
            and q.get("below0" if zero else "below51") is True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--e4-plan", type=Path,
                    default=OUT / "P9-Q8-E4-complete-plan-v9.json")
    ap.add_argument("--e3-progress", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    require(not args.output.exists(), "Refusing to overwrite an immutable plan")
    tracked = {}
    def bind(path, expected=None):
        path = Path(path).resolve()
        h = sha(path)
        require(expected is None or h == expected, "Changed named input: " + str(path))
        require(path not in tracked or tracked[path] == h, "Input changed during preparation")
        tracked[path] = h
        return dict(path=str(path), sha256=h)
    def read(path, expected=None):
        bind(path, expected)
        return json.loads(Path(path).read_text())

    plan = read(args.e4_plan, E4_PLAN_SHA)
    require(plan.get("schema") == "d17-stage-proof-plan-v1"
            and plan.get("kind") == "P9-Q8" and not plan.get("unproved_candidates")
            and len(plan.get("nodes", [])) == 70, "Wrong completed E4 antecedent plan")
    original_nodes = json.loads(json.dumps(plan["nodes"]))
    ancestor_ids = [n["id"] for n in original_nodes]
    require(set(ancestor_ids) == ({f"Y-IY{i:02d}" for i in range(4)}
            | {f"Z-IZ{i:02d}" for i in range(8)}
            | {f"four-E4_{i:02d}" for i in range(58)})
            and len(set(ancestor_ids)) == 70, "Unexpected E4 node identities")
    progress = read(args.e3_progress)
    require(progress.get("kind") == "P9-Q8" and progress.get("stage") == "E3"
            and progress.get("source_sha256") == V9
            and progress.get("antecedent_plan") == bind(args.e4_plan, E4_PLAN_SHA)
            and progress.get("completed") == progress.get("total") == 24
            and len(progress.get("records", [])) == 24,
            "E3 progress is incomplete or has different antecedents")
    rows = {r["case"]: r for r in progress["records"]}
    require(len(rows) == 24 and set(rows) == {f"E3_{i:02d}" for i in range(24)},
            "E3 case domain is not exactly00..23")
    yzero = [15,23,27,29,30,39,43,45,46,51,53,54,57,58,60]
    new_receipts = set()
    for case in sorted(rows):
        item = rows[case]
        path = Path(item["path"]).resolve()
        d = read(path, item["sha256"])
        require(d.get("kind") == "P9-Q8" and d.get("case") == case
                and d.get("source_sha256") == V9 and strict(d)
                and d.get("empty_z") is True and d.get("assigned_z") is None
                and d.get("forbid_four_core") is True and d.get("forbidden") == yzero
                and d.get("extra_members") == [] and d.get("h27_cliques") is None
                and d.get("degree_distributions") is False
                and d.get("crowding_imports") is True,
                "E3 leaf is nonstrict or has different actual/absence premises: " + case)
        if d.get("certificate_kind") == "zero-infeasibility":
            original = read(d["input_receipt_path"], d["input_receipt_sha256"])
            require(d.get("certificate_producer_sha256") == PHASE
                    and d.get("original_status") == original.get("status") == 2,
                    "Phase-one leaf lacks its named original status2 input")
            changed = {"status", "message", "assurance", "dual", "primal_trace"}
            require(all(d.get(k) == v for k,v in original.items() if k not in changed),
                    "Phase-one leaf changed original E3 premises")
        else:
            require(d.get("certificate_kind") in (None, "trace-upper-bound"),
                    "Unsupported E3 certificate kind")
        replay = (HERE / "degree17_full_replay" / (path.stem + "-replay.json")).resolve()
        node = dict(id="three-" + case, receipt=str(path), receipt_sha256=item["sha256"],
                    replay=str(replay), uses=list(ancestor_ids))
        if replay.exists():
            node["replay_sha256"] = sha(replay)
        plan["nodes"].append(node)
        new_receipts.add(path)
    require(plan["nodes"][:70] == original_nodes and len(plan["nodes"]) == 94,
            "Existing E4 nodes changed during append")
    require(all(n["uses"] == ancestor_ids for n in plan["nodes"][70:]),
            "E3 siblings acquired unintended ancestry")
    bind(__file__)
    construction = {Path(b["path"]).resolve(): b["sha256"]
                    for b in plan.get("construction_inputs", [])}
    construction.update({p:h for p,h in tracked.items() if p not in new_receipts})
    plan["construction_inputs"] = [dict(path=str(p), sha256=h)
        for p,h in sorted(construction.items(), key=lambda z:str(z[0]))]
    for path,h in tracked.items():
        require(sha(path) == h, "Input changed while appending: " + str(path))
    with args.output.open("x") as f:
        json.dump(plan, f, indent=2, allow_nan=False)
        f.write("\n")
    print(json.dumps(dict(status="PREPARED_94_NODE_Q8_PLAN_REPLAY_AND_COVERAGE_REQUIRED",
                         output=str(args.output.resolve()), output_sha256=sha(args.output),
                         unchanged_E4_nodes=70, new_E3_nodes=24, E3_sibling_ancestry=False,
                         no_model_solver_or_replay_execution=True)))


if __name__ == "__main__":
    main()
