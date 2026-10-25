#!/usr/bin/env python3
"""Prepare sibling Q8 E4_56/57 branches using exactly the strict00..55 orbits.

Standard-library metadata/literal-orbit work only; no model, solver, numerical
replay or compilation.  The generated plan requires exact replay and the
existing stage checker before the new exclusions may be treated as proved.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
OUT = HERE / "degree17_full"
V9 = "31368d8392328daa9f161b23e40ef7c3df3d9acd4743cf4914f9df0215b74eb2"
CHECKER = "e8553f1726e58d30032294c4e96711a1c3507d4cb381ad532982c1a4003f805b"
INTERNAL_PLAN = "9a342f00a1fe948618c6e6bf8ed87239a8d6aa6ef1555e3cd29d95167a82430f"


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
    ap.add_argument("--progress", type=Path,
        default=OUT / "P9-Q8-exterior-E4-v9-progress.json")
    ap.add_argument("--internal-plan", type=Path,
        default=OUT / "P9-Q8-internal-plan-v9.json")
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--completed-stage1-receipt", type=Path, action="append", default=[])
    args = ap.parse_args()
    request_path = args.output.with_name(args.output.stem + "-requests.json")
    forbidden_path = args.output.with_name(args.output.stem + "-forbidden.json")
    require(all(not p.exists() for p in (args.output, request_path, forbidden_path)),
            "Refusing to replace a prepared immutable plan or request")
    tracked = {}
    def bind(path, expected=None):
        path = Path(path).resolve()
        h = sha(path)
        require(expected is None or h == expected, "Input hash mismatch: " + str(path))
        require(path not in tracked or tracked[path] == h, "Input changed")
        tracked[path] = h
        return dict(path=str(path), sha256=h)
    def read(path, expected=None):
        bind(path, expected)
        return json.loads(Path(path).read_text())

    checker_path = HERE / "check_d17_stage_plan_v9.py"
    bind(checker_path, CHECKER)
    spec = importlib.util.spec_from_file_location("q8_stage_literal_only", checker_path)
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    cert_path = checker.PRIOR / "repository/companion/terminal/r16/results/seven_certificate.json"
    g = checker.reconstruct("P9-Q8", read(cert_path, checker.I7_CERT))
    plan = read(args.internal_plan, INTERNAL_PLAN)
    require(plan.get("kind") == "P9-Q8" and not plan.get("unproved_candidates")
            and len(plan["nodes"]) == 12, "Wrong internal antecedent plan")
    internal_ids = [n["id"] for n in plan["nodes"]]
    require(set(internal_ids) == {"Y-IY%02d" % i for i in range(4)}
            | {"Z-IZ%02d" % i for i in range(8)}, "Internal node domain differs")
    progress = read(args.progress)
    require(progress.get("kind") == "P9-Q8" and progress.get("stage") == "E4"
            and progress.get("source_sha256") == V9
            and progress.get("antecedent_plan") == bind(args.internal_plan, INTERNAL_PLAN),
            "Wrong initial E4 progress ancestry")
    rows = {r["case"]: r for r in progress["records"]}
    require(len(rows) == len(progress["records"])
            and set(rows) == {f"E4_{i:02d}" for i in range(58)},
            "Expected exactly the original58 discovery branches")
    yzero = sorted(g["y_four"])
    required = [f"E4_{i:02d}" for i in range(56)]
    open_cases = ["E4_56", "E4_57"]
    receipt_paths = {Path(n["receipt"]).resolve() for n in plan["nodes"]}

    def add(nid, path, expected, uses, forbidden):
        d = read(path, expected)
        require(d.get("kind") == "P9-Q8" and d.get("source_sha256") == V9
                and strict(d) and d.get("case") == nid.split("four-")[-1]
                and d.get("forbidden") == forbidden and d.get("empty_z") is True
                and d.get("assigned_z") is None and d.get("forbid_four_core") is False
                and d.get("extra_members") == [] and d.get("h27_cliques") is None
                and d.get("crowding_imports") is True
                and d.get("degree_distributions") is False,
                "Strict leaf has different branch premises: " + nid)
        require(d["geometry"]["records"] == g["records"], "Literal marker census mismatch")
        path = Path(path).resolve()
        replay = HERE / "degree17_full_replay" / (path.stem + "-replay.json")
        node = dict(id=nid, receipt=str(path), receipt_sha256=sha(path),
                    replay=str(replay.resolve()), uses=list(uses))
        if replay.exists():
            node["replay_sha256"] = sha(replay)
        plan["nodes"].append(node)
        receipt_paths.add(path)
        return d

    forbidden = set(yzero)
    for case in required:
        item = rows[case]
        add("four-" + case, item["path"], item["sha256"], internal_ids, yzero)
        forbidden.update(g["records"][case]["orbit"])
    forbidden = sorted(forbidden)
    require(len(forbidden) == 662 and len(g["records"]["E4_56"]["orbit"]) == 9
            and len(g["records"]["E4_57"]["orbit"]) == 9,
            "Unexpected stage1 orbit counts")
    require(not set(forbidden) & {s for c in open_cases for s in g["records"][c]["orbit"]},
            "Circular exclusion of a currently open orbit")
    preceding_ids = [n["id"] for n in plan["nodes"]]
    require(len(preceding_ids) == 68, "Wrong sibling ancestry size")
    completed = set()
    for path in args.completed_stage1_receipt:
        d = read(path)
        case = d.get("case")
        require(case in open_cases and case not in completed, "Duplicate or alien stage1 leaf")
        # Both siblings use the same strictly earlier68 nodes. Neither
        # becomes an ancestor of the other, regardless of argument order.
        add("four-" + case, path, sha(path), preceding_ids, forbidden)
        completed.add(case)
    construction = {Path(b["path"]).resolve(): b["sha256"]
                    for b in plan.get("construction_inputs", [])}
    construction.update({p:h for p,h in tracked.items() if p not in receipt_paths})
    plan["construction_inputs"] = [dict(path=str(p), sha256=h)
                                   for p,h in sorted(construction.items(), key=lambda z:str(z[0]))]
    plan["unproved_candidates"] = []
    source = bind(HERE / "degree17_full_projection_v9.py", V9)
    requests = dict(
        status="PREPARED_SIBLING_DISCOVERY_REQUESTS_REPLAYS_AND_STAGE_VALIDATION_REQUIRED",
        kind="P9-Q8", plan=dict(path=str(args.output.resolve())),
        source=source, checker=bind(checker_path, CHECKER),
        prior_strict_cases=required, same_antecedents_for_both=preceding_ids,
        forbidden_count=len(forbidden), empty_z=True,
        requests=[dict(case=c, actual_marker=g["records"][c]["marker"],
                       orbit=g["records"][c]["orbit"], forbidden=forbidden,
                       empty_z=True, forbid_four_core=False,
                       label="exterior-E4-stage1-v9", completed=c in completed,
                       solver_argv=[sys.executable, source["path"], "--kind", "P9-Q8",
                           "--case", c, "--solve", "--seconds", "20", "--empty-z",
                           "--label", "exterior-E4-stage1-v9", "--forbidden",
                           json.dumps(forbidden, separators=(",", ":"))]) for c in open_cases],
        no_sibling_assumption=True,
        assurance="Producer strictness is only a diagnostic until exact replay and literal ancestry validation.")
    for path, h in tracked.items():
        require(sha(path) == h, "Input changed during preparation")
    for path, data in ((args.output, plan), (forbidden_path, forbidden), (request_path, requests)):
        with path.open("x") as f:
            json.dump(data, f, indent=2, allow_nan=False)
            f.write("\n")
    print(json.dumps(dict(plan=str(args.output.resolve()), nodes=len(plan["nodes"]),
                         requests=str(request_path.resolve()), forbidden_count=len(forbidden),
                         completed_stage1=sorted(completed), no_numerical_execution=True)))


if __name__ == "__main__":
    main()
