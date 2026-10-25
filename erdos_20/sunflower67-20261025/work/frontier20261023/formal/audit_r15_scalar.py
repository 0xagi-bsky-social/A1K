"""Fail-closed audit of the observed five-root Lean compiler output."""
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOTS = ["outer_deletion_scalar_impossible", "hub_strict_triangle_impossible",
         "hub_deletion_scalar_impossible", "rho_six_support_le_eleven",
         "rho_six_requires_degree_five"]

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    src = HERE / "R15ScalarClosure.lean"
    obj = HERE / "build/R15ScalarClosure.olean"
    receipt = HERE / "receipts/R15ScalarClosure.bounded.json"
    log = HERE / "receipts/R15ScalarClosure.bounded.log"
    runtime = HERE.parents[2] / "work/frontier20261019/runtime.json"
    d = json.loads(receipt.read_text())
    if not (d["exit_code"] == 0 and d["status"] == "completed" and d["source_stable"]
            and d["source_sha256"] == sha(src) and d["object_sha256"] == sha(obj)
            and d["output_sha256"] == sha(log)):
        raise ValueError("Compilation receipt or current source/object/log disagrees")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    roots = {}
    for line in log.read_text().splitlines():
        m = re.fullmatch(r"'FrontierR15\.([A-Za-z_]+)' depends on axioms: \[([^\]]*)\]", line)
        if m is None:
            if line.strip():
                raise ValueError("Unexpected compiler output: " + line)
            continue
        name, content = m.groups()
        axioms = set(content.split(", ")) if content else set()
        if name not in ROOTS or name in roots or not axioms <= allowed:
            raise ValueError("Unexpected, duplicate, or disallowed root/axiom")
        roots[name] = sorted(axioms)
    if set(roots) != set(ROOTS):
        raise ValueError("Missing required roots")
    out = dict(status="PASS", assurance="axiom-audited", module="R15ScalarClosure",
               source_sha256=sha(src), object_sha256=sha(obj),
               compilation_receipt_sha256=sha(receipt), log_sha256=sha(log),
               auditor_sha256=sha(Path(__file__)), runtime_manifest_sha256=sha(runtime),
               roots=roots, allowed_axioms=sorted(allowed), repairs=0,
               limitations="Five literal arithmetic implications only; geometric premises remain separate. Existing pinned dependency cache, not clean replay or independent reproduction.")
    with (HERE / "receipts/R15ScalarClosure.axiom-audit.json").open("x") as f:
        json.dump(out, f, indent=2)
        f.write("\n")
    print(json.dumps(dict(status="PASS", roots=len(roots), source_sha256=sha(src))))

if __name__ == "__main__":
    main()
