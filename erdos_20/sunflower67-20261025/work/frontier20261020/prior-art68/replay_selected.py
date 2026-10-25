"""Replay selected external finite suites; never report complete theorem validation."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import subprocess
import sys
import time

BASE = Path(__file__).resolve().parent
PACKAGE = BASE / "replay-quick-20261020/package"
OUT = BASE / "replay-selected-20261020"
IDS = ("terminal.cross15", "terminal.crowding", "terminal.cap61", "terminal.r16")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def canonical(data):
    return json.dumps(data, sort_keys=True, ensure_ascii=False,
                      separators=(",", ":")).encode()


def verify_inputs():
    manifest = json.loads((PACKAGE / "COMPUTATIONAL_MANIFEST.json").read_bytes())
    for row in manifest["files"]:
        path = (PACKAGE / row["path"]).resolve()
        if not path.is_relative_to(PACKAGE):
            raise ValueError("Input outside package")
        data = path.read_bytes()
        if len(data) != row["bytes"] or digest(data) != row["sha256"]:
            raise ValueError("Input mismatch: " + row["path"])
    return {"files": len(manifest["files"]),
            "manifest_sha256": digest((PACKAGE / "COMPUTATIONAL_MANIFEST.json").read_bytes())}


def main():
    OUT.mkdir(exist_ok=False)
    record = {
        "status": "RUNNING",
        "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "python": sys.version,
        "selected_ids": IDS,
        "executions": [],
        "complete_companion": False,
        "written_reductions_formalized": False,
        "external_H27_or_Jin_replayed": False,
        "independent_human_validation": False,
        "scope": "Four selected exact finite suites only; original unchanged external checkers.",
    }

    def save():
        (OUT / "RECEIPT.json").write_text(
            json.dumps(record, ensure_ascii=False, indent=2) + "\n")

    save()
    try:
        record["inputs_before"] = verify_inputs()
        plan = json.loads((PACKAGE / "SUITE_PLAN.json").read_bytes())
        suites = {c["id"]: c for c in plan["commands"]}
        env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1", PYTHONHASHSEED="0",
                   PYTHONUTF8="1")
        for sid in IDS:
            suite = suites[sid]
            if suite["volatile_keys"] or suite["json_source"] != "stdout":
                raise ValueError("Unexpected selected-suite output contract")
            for optimized in (False, True):
                mode = "optimized" if optimized else "normal"
                job = OUT / (sid.replace(".", "_") + "_" + mode)
                job.mkdir()
                command = [sys.executable, "-B"]
                if optimized:
                    command.append("-O")
                command += ["-X", "utf8", str(PACKAGE / "scripts/guarded_checker.py"),
                            str(OUT), *suite["argv"]]
                item = {"id": sid, "mode": mode, "argv": command,
                        "cwd": str(PACKAGE / suite.get("cwd", ".")),
                        "timeout_seconds": 120}
                start = time.monotonic()
                try:
                    result = subprocess.run(
                        command, cwd=item["cwd"], env=env,
                        capture_output=True, timeout=120)
                    stdout, stderr = result.stdout, result.stderr
                    item["returncode"] = result.returncode
                except subprocess.TimeoutExpired as exc:
                    stdout, stderr = exc.stdout or b"", exc.stderr or b""
                    item["status"] = "TIMEOUT"
                    result = None
                (job / "stdout.json").write_bytes(stdout)
                (job / "stderr.txt").write_bytes(stderr)
                item.update(elapsed_seconds=time.monotonic() - start,
                            stdout_sha256=digest(stdout), stderr_sha256=digest(stderr))
                record["executions"].append(item)
                save()
                if result is None or result.returncode != 0:
                    raise ValueError("Execution failed: " + sid + " " + mode)
                actual = json.loads(stdout)
                if canonical(actual) != canonical(suite["expected_semantic"]):
                    raise ValueError("Exact semantic mismatch: " + sid)
                item.update(status="PASS_EXPECTED_SEMANTICS",
                            semantic_sha256=digest(canonical(actual)))
                save()
                print(sid, mode, item["status"], flush=True)
        record["inputs_after"] = verify_inputs()
        if record["inputs_before"] != record["inputs_after"]:
            raise ValueError("Inputs changed")
        record["status"] = "SELECTED_FOUR_SUITE_PARTIAL_PASS"
    except Exception as exc:
        record.update(status="FAIL_INCOMPLETE", error=repr(exc))
    record["finished_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    save()
    print(record["status"], flush=True)
    return 0 if record["status"] == "SELECTED_FOUR_SUITE_PARTIAL_PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
