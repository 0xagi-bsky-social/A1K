#!/usr/bin/env python3
"""Pinned, resumable local Lean replay. No downloads or publication authority.

The caller must authenticate/retain the expected manifest AND policy digests
outside the files being checked. Local hashes are byte commitments, not signatures.
The policy is a separately frozen record; this runner never generates one for itself.
"""
from __future__ import annotations

import argparse
import ctypes
import fcntl
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import signal
import subprocess
import sys
import time
import uuid

SCHEMA = "erdos20-replay-policy/1"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PACKAGES = {"mathlib", "plausible", "LeanSearchClient", "importGraph", "proofwidgets", "aesop", "Qq", "batteries", "Cli"}
DIGEST = re.compile(r"[0-9a-f]{64}")


class ReplayError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise ReplayError(message)


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def commitment(value):
    return hashlib.sha256(canonical(value)).hexdigest()


def strict_json(path):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, "duplicate JSON key: " + key)
            result[key] = value
        return result
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs,
                      parse_constant=lambda value: (_ for _ in ()).throw(ReplayError("non-finite JSON")))


def contained(root, relative):
    require(isinstance(relative, str) and relative, "empty/non-string path")
    part = PurePosixPath(relative)
    require(not part.is_absolute() and ".." not in part.parts and str(part) == relative,
            "noncanonical or escaping path: " + relative)
    path = root / relative
    current = root
    for item in part.parts:
        current = current / item
        require(not current.is_symlink(), "symlink forbidden in committed input: " + relative)
    require(path.resolve().is_relative_to(root.resolve()), "path escapes root")
    return path


def tree_digest(root):
    """Hash exact paths and bytes, including non-object auxiliary inputs."""
    root = Path(root)
    require(root.is_dir() and not root.is_symlink(), "committed tree missing or symlinked: " + str(root))
    rows = []
    for path in sorted(root.rglob("*")):
        if path.is_symlink():
            target = path.resolve(strict=True)
            require(target.is_relative_to(root.resolve()) and target.is_file(), "escaping/directory symlink in committed tree")
            rows.append([path.relative_to(root).as_posix(), "symlink", os.readlink(path), sha(target)])
        elif path.is_file():
            rows.append([path.relative_to(root).as_posix(), sha(path)])
        else:
            require(path.is_dir(), "special file in committed tree")
    return {"sha256": commitment(rows), "file_count": len(rows)}


def atomic_json(path, value, *, exclusive=False):
    path = Path(path)
    temp = path.with_name(path.name + ".tmp-" + uuid.uuid4().hex)
    with temp.open("xb") as handle:
        handle.write(canonical(value) + b"\n")
        handle.flush()
        os.fsync(handle.fileno())
    if exclusive:
        try:
            os.link(temp, path)
        finally:
            temp.unlink()
    else:
        os.replace(temp, path)
    descriptor = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def verify_manifest(root, expected_sha, metadata_files):
    require(DIGEST.fullmatch(expected_sha) is not None, "expected manifest digest required")
    path = contained(root, "source_manifest.json")
    require(sha(path) == expected_sha, "source manifest external commitment mismatch")
    manifest = strict_json(path)
    require(isinstance(manifest, dict) and manifest, "empty/non-object source manifest")
    require(isinstance(metadata_files, list) and len(metadata_files) == len(set(metadata_files)), "invalid metadata coverage")
    required = set(metadata_files)
    require({"lake-manifest.json", "lakefile.toml", "lean-toolchain", "evidence/axiom_audit_inventory.json"} <= required,
            "policy omits mandatory build/audit metadata")
    for directory in ["SunflowerLean", "negative"]:
        folder = contained(root, directory)
        require(folder.is_dir(), "required source directory missing")
        found = {p.relative_to(root).as_posix() for p in folder.rglob("*.lean")}
        require(found, "protected source directory is empty: " + directory)
        required |= found
    require(set(manifest) == required, "source manifest must have exact protected path coverage")
    for name, digest in manifest.items():
        require(isinstance(digest, str) and DIGEST.fullmatch(digest), "malformed source digest")
        source = contained(root, name)
        require(source.is_file() and sha(source) == digest, "source hash mismatch: " + name)
    return manifest


def command_text(argv, cwd=None):
    result = subprocess.run(argv, cwd=cwd, stdin=subprocess.DEVNULL, capture_output=True,
                            text=True, timeout=60, env={"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8"})
    require(result.returncode == 0, "identity command failed: " + argv[0])
    return result.stdout.strip()


def dynamic_libraries(lean):
    output = command_text(["/usr/bin/ldd", str(lean)])
    libraries = {}
    for line in output.splitlines():
        require("not found" not in line, "missing dynamic library")
        match = re.search(r"(?:=>\s+)?(/[^\s]+)\s+\(", line)
        if match:
            path = Path(match.group(1)).resolve()
            libraries[str(path)] = sha(path)
    require(libraries, "dynamic runtime inventory empty")
    return libraries


def dependency_identity(root, packages):
    lock = strict_json(root / "lake-manifest.json")["packages"]
    require(len(lock) == 9 and {item["name"] for item in lock} == PACKAGES, "nine-package lock mismatch")
    require({p.name for p in packages.iterdir()} == PACKAGES, "extra/missing dependency directory")
    result = {}
    paths = []
    seen_objects = set()
    for item in sorted(lock, key=lambda item: item["name"]):
        folder = contained(packages, item["name"])
        require(folder.is_dir(), "dependency directory missing")
        revision = command_text(["/usr/bin/git", "rev-parse", "HEAD"], folder)
        require(revision == item["rev"], "dependency revision mismatch: " + item["name"])
        require(not command_text(["/usr/bin/git", "status", "--porcelain", "--untracked-files=no"], folder),
                "tracked dependency sources are dirty: " + item["name"])
        cache = folder / ".lake/build/lib/lean"
        if cache.exists():
            require(not (cache / "SunflowerLean").exists(), "dependency shadows project namespace")
            objects = {p.relative_to(cache).as_posix() for p in cache.rglob("*.olean")}
            require(not (objects & seen_objects), "conflicting module objects across dependencies")
            seen_objects |= objects
        cache_id = tree_digest(cache) if cache.exists() else {"sha256": commitment([]), "file_count": 0}
        result[item["name"]] = {"revision": revision, "cache": cache_id}
        if cache.exists():
            paths.append(cache.resolve())
    return result, paths


def verify_environment(root, lean, packages, policy):
    require(sha(Path(__file__).resolve()) == policy["harness_sha256"], "replay harness identity mismatch")
    require(sha(lean) == policy["compiler_sha256"], "compiler binary identity mismatch")
    version = command_text([str(lean), "--version"])
    require(version == policy["compiler_version"], "complete compiler version mismatch")
    runtime = tree_digest(lean.parent.parent / "lib")
    require(runtime == policy["toolchain_lib_tree"], "toolchain libraries/stdlib identity mismatch")
    dynamic = dynamic_libraries(lean)
    require(dynamic == policy["dynamic_libraries"], "dynamic library identity mismatch")
    dependencies, paths = dependency_identity(root, packages)
    require(dependencies == policy["dependencies"], "dependency cache identity mismatch")
    options = policy["lean_options"]
    require(isinstance(options, list) and all(isinstance(x, str) and re.fullmatch(r"-D[A-Za-z0-9_.]+=[A-Za-z0-9_.-]+", x) for x in options),
            "only explicit -D Lean options are allowed")
    return {"compiler_sha256": sha(lean), "compiler_version": version, "toolchain_lib_tree": runtime,
            "dynamic_libraries": dynamic, "dependencies": dependencies, "lean_options": options,
            "harness_sha256": policy["harness_sha256"], "environment": {"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8"}}, paths


def import_order(root, manifest):
    """Read this release's restricted, one-line import syntax; reject cycles."""
    paths = {name[:-5].replace("/", "."): name for name in manifest if name.startswith("SunflowerLean/") and name.endswith(".lean")}
    graph = {}
    for module, name in paths.items():
        # Strip nested Lean block comments before recognizing import lines.
        text = (root / name).read_text(); clean = []; depth = 0; index = 0
        while index < len(text):
            pair = text[index:index+2]
            if pair == "/-": depth += 1; index += 2; continue
            if pair == "-/" and depth: depth -= 1; index += 2; continue
            clean.append(text[index] if not depth or text[index] == "\n" else " "); index += 1
        require(depth == 0, "unclosed block comment")
        dependencies = []
        for line in "".join(clean).splitlines():
            line = line.split("--", 1)[0].strip()
            if line.startswith("import "):
                names = line.removeprefix("import ").split()
                require(names and all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", x) for x in names), "unsupported import syntax")
                for target in names:
                    if target.startswith("SunflowerLean."):
                        require(target in paths, "missing local import: " + target)
                        dependencies.append(target)
        graph[module] = dependencies
    order = []; visiting = set(); done = set()
    def visit(module):
        require(module not in visiting, "cyclic import graph")
        if module in done: return
        visiting.add(module)
        for dependency in sorted(graph[module]): visit(dependency)
        visiting.remove(module); done.add(module); order.append(module)
    for module in sorted(paths): visit(module)
    return order, paths


def diagnostic_records(output):
    records = []
    for line in output.splitlines():
        if not line.strip(): continue
        try: item = json.loads(line)
        except json.JSONDecodeError: raise ReplayError("non-JSON compiler diagnostic") from None
        require(isinstance(item, dict) and "severity" in item, "unrecognized compiler diagnostic")
        records.append(item)
    return records


def negative_matches(records, fixture, root, exit_code):
    errors = [item for item in records if item.get("severity") == "error"]
    if exit_code != 1 or len(errors) != 1:
        return False
    item = errors[0]
    filename = item.get("fileName", "")
    if not filename:
        return False
    diagnostic_path = Path(filename)
    if not diagnostic_path.is_absolute(): diagnostic_path = root / diagnostic_path
    return (diagnostic_path.resolve() == contained(root, fixture["path"]).resolve()
            and fixture["line_start"] <= item.get("pos", {}).get("line", -1) <= fixture["line_end"]
            and re.fullmatch(fixture["message_pattern"], item.get("data", ""), re.DOTALL) is not None)


def execute_attempt(run, command, cwd, env, identity, timeout, max_log_bytes):
    # Linux subreaper ensures ordinary orphaned compiler descendants are reaped.
    require(sys.platform.startswith("linux"), "this runner requires Linux wait4/subreaper semantics")
    require(ctypes.CDLL(None, use_errno=True).prctl(36, 1, 0, 0, 0) == 0, "cannot enable child subreaper")
    attempt_id = uuid.uuid4().hex
    stem = run / "attempts" / attempt_id
    started = {"attempt_id": attempt_id, "status": "started", "identity": identity,
               "command": command, "started_unix_seconds": time.time(), "timeout_seconds": timeout,
               "max_log_bytes": max_log_bytes}
    atomic_json(stem.with_suffix(".started.json"), started, exclusive=True)
    log = stem.with_suffix(".jsonl")
    start = time.monotonic(); state = "failed"; code = None; usage = None; process = None; descendant_usage = []; launch_error = None
    with log.open("xb") as output:
        try:
            process = subprocess.Popen(command, cwd=cwd, env=env, stdin=subprocess.DEVNULL,
                                       stdout=output, stderr=output, start_new_session=True)
            while True:
                pid, status, measured = os.wait4(process.pid, os.WNOHANG)
                if pid:
                    usage = measured; code = os.waitstatus_to_exitcode(status); process.returncode = code
                    state = "completed" if code == 0 else "failed"; break
                if time.monotonic() - start >= timeout: state = "timed_out"; break
                if log.stat().st_size > max_log_bytes: state = "log_limit"; break
                time.sleep(0.02)
        except KeyboardInterrupt:
            state = "interrupted"
        except OSError as exc:
            state = "launch_failed"; launch_error = str(exc)
        finally:
            if process is not None:
                # Always clean this isolated process group, including descendants.
                try: os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError: pass
                if process.returncode is None:
                    _, status, usage = os.wait4(process.pid, 0)
                    code = os.waitstatus_to_exitcode(status); process.returncode = code
                while True:
                    try:
                        child, _, measured = os.wait4(-process.pid, 0)
                    except ChildProcessError:
                        break
                    if child: descendant_usage.append(measured)
            output.flush(); os.fsync(output.fileno())
    receipt = dict(started, status=state, exit_code=code, wall_seconds=time.monotonic()-start,
                   log_path=log.relative_to(run).as_posix(), log_sha256=sha(log),
                   cpu_user_seconds=sum(x.ru_utime for x in ([usage] if usage else []) + descendant_usage),
                   cpu_system_seconds=sum(x.ru_stime for x in ([usage] if usage else []) + descendant_usage),
                   peak_rss_kib=max((x.ru_maxrss for x in ([usage] if usage else []) + descendant_usage), default=None),
                   orphaned_descendants_reaped=len(descendant_usage),
                   launch_error=launch_error,
                   resource_scope="direct compiler process plus children reaped by that process; escaped descendants are outside this local process-group boundary")
    atomic_json(stem.with_suffix(".receipt.json"), receipt, exclusive=True)
    return receipt


def record_status(run, status, context_hash, receipts, **extra):
    value = {"run_id": run.name, "status": status, "context_sha256": context_hash,
             "receipt_ids": [item["attempt_id"] for item in receipts],
             "receipts_sha256": commitment(receipts), "charged_attempt_wall_seconds": sum(item["wall_seconds"] for item in receipts),
             "updated_unix_seconds": time.time(), **extra}
    atomic_json(run / "events" / (uuid.uuid4().hex + ".json"), value, exclusive=True)
    atomic_json(run / "status.json", value)
    return value


def prior_receipts(run, context_hash):
    context = strict_json(run / "context.json")
    require(commitment(context) == context_hash, "resume full context mismatch")
    status = strict_json(run / "status.json")
    require(status["context_sha256"] == context_hash and status["run_id"] == run.name, "resume status context/run mismatch")
    require(status["status"] != "completed", "completed run is immutable; start a new run")
    receipts = []
    for name in status["receipt_ids"]:
        enriched = run / "attempts" / (name + ".validated.json")
        original = strict_json(run / "attempts" / (name + ".receipt.json"))
        item = strict_json(enriched) if enriched.exists() else original
        started = strict_json(run / "attempts" / (name + ".started.json"))
        require(item["attempt_id"] == name and original["attempt_id"] == name, "resume attempt identity mismatch")
        require(all(item.get(k) == v for k, v in original.items()), "enrichment changes process receipt")
        require(all(original.get(k) == v for k, v in started.items() if k != "status"), "process receipt changes started attempt")
        require(sha(contained(run, item["log_path"])) == item["log_sha256"], "resume diagnostic log mismatch")
        receipts.append(item)
    require(commitment(receipts) == status["receipts_sha256"], "resume receipt chain mismatch")
    actual_ids = {p.name.removesuffix(".receipt.json") for p in (run / "attempts").glob("*.receipt.json")}
    require(len(status["receipt_ids"]) == len(set(status["receipt_ids"])) and actual_ids == set(status["receipt_ids"]),
            "resume index omits or duplicates finalized attempts; explicit reconciliation required")
    for started in (run / "attempts").glob("*.started.json"):
        require(started.with_name(started.name.replace(".started.json", ".receipt.json")).exists(),
                "unfinalized interrupted attempt requires explicit reconciliation; history retained")
    return receipts


def replay(args):
    root = args.root.resolve(); policy_path = args.policy.resolve()
    require(DIGEST.fullmatch(args.expected_policy_sha256) and sha(policy_path) == args.expected_policy_sha256,
            "reproduction policy external commitment mismatch")
    policy = strict_json(policy_path)
    require(policy["schema"] == SCHEMA, "wrong reproduction policy schema")
    require(sha(Path(__file__).resolve()) == policy["harness_sha256"], "replay harness identity mismatch")
    manifest = verify_manifest(root, args.expected_manifest_sha256, policy["metadata_files"])
    order, sources = import_order(root, manifest)
    fixtures = policy["negative_fixtures"]
    require(fixtures and {f["path"] for f in fixtures} == {p for p in manifest if p.startswith("negative/")}, "negative policy coverage mismatch")
    require(len(fixtures) == len({f["path"] for f in fixtures}), "duplicate negative fixture policy")
    for fixture in fixtures:
        require(isinstance(fixture["line_start"], int) and isinstance(fixture["line_end"], int)
                and 1 <= fixture["line_start"] <= fixture["line_end"], "invalid negative target span")
        require(isinstance(fixture["message_pattern"], str) and 1 <= len(fixture["message_pattern"]) <= 10000,
                "invalid negative diagnostic pattern")
        re.compile(fixture["message_pattern"])
    if args.check_only:
        print(json.dumps({"status": "source-commitments-checked", "manifest_sha256": args.expected_manifest_sha256,
                          "file_count": len(manifest), "module_count": len(order), "compiled": False}))
        return 0
    require(args.lean and args.packages, "compilation requires explicit --lean and --packages")
    lean = args.lean.resolve(); packages = args.packages.resolve()
    environment, dep_paths = verify_environment(root, lean, packages, policy)
    context = {"manifest_sha256": args.expected_manifest_sha256, "policy_sha256": args.expected_policy_sha256,
               "environment": environment, "root": str(root), "lean": str(lean), "packages": str(packages),
               "module_order": order, "module_timeout_seconds": args.module_timeout, "wall_budget_seconds": args.wall_budget,
               "max_log_bytes": args.max_log_bytes}
    context_hash = commitment(context)
    args.runs.mkdir(parents=True, exist_ok=True)
    run = args.runs.resolve() / (args.resume or (time.strftime("%Y%m%dT%H%M%S") + "-" + uuid.uuid4().hex))
    require(run.parent == args.runs.resolve(), "invalid resume run ID")
    if not args.resume:
        run.mkdir(); (run / "objects").mkdir(); (run / "attempts").mkdir(); (run / "events").mkdir()
        atomic_json(run / "context.json", context, exclusive=True)
    with (run / "run.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        receipts = prior_receipts(run, context_hash) if args.resume else []
        env = dict(environment["environment"], LEAN_PATH=os.pathsep.join(map(str, [run / "objects"] + dep_paths)))
        completed = {}
        for item in receipts:
            identity = item["identity"]
            require(identity["kind"] in {"module", "negative"}, "resume unknown attempt kind")
            if identity["kind"] == "module":
                require(identity["module"] in sources, "resume unknown module")
                source_name = sources[identity["module"]]
                expected_command = [str(lean), "--json", *policy["lean_options"], "-o",
                    str(run / "objects" / (identity["module"].replace(".", "/") + ".olean")), str(root / source_name)]
            else:
                source_name = identity["fixture"]
                require(source_name in {f["path"] for f in fixtures}, "resume unknown negative fixture")
                expected_command = [str(lean), "--json", *policy["lean_options"], str(root / source_name)]
            require(identity["source_sha256"] == manifest[source_name], "resume source identity mismatch")
            require(item["command"] == expected_command, "resume compiler/command/options mismatch")
            if identity["kind"] == "module" and item["status"] == "completed":
                require(item["exit_code"] == 0, "completed compiler receipt has failure exit")
                obj = run / "objects" / (identity["module"].replace(".", "/") + ".olean")
                require(sha(obj) == item["olean_sha256"], "resume object mismatch")
                completed[identity["module"]] = item
        require(list(completed) == order[:len(completed)], "resume compilation order mismatch")
        record_status(run, "running", context_hash, receipts)
        try:
            for module in order[len(completed):]:
                charged = sum(item["wall_seconds"] for item in receipts)
                if charged >= args.wall_budget:
                    record_status(run, "budget_exhausted", context_hash, receipts); return 2
                src = root / sources[module]; obj = run / "objects" / (module.replace(".", "/") + ".olean")
                require(sha(src) == manifest[sources[module]], "source drift before compiler: " + module)
                obj.parent.mkdir(parents=True, exist_ok=True)
                # Failed attempts may leave a partial object; never import it on retry.
                obj.unlink(missing_ok=True)
                command = [str(lean), "--json", *policy["lean_options"], "-o", str(obj), str(src)]
                item = execute_attempt(run, command, root, env,
                    {"kind": "module", "module": module, "source_sha256": sha(src)},
                    min(args.module_timeout, args.wall_budget-charged), args.max_log_bytes)
                receipts.append(item)
                require(sha(src) == manifest[sources[module]], "source drift during compiler: " + module)
                if item["status"] == "completed":
                    require(obj.is_file(), "compiler returned success without object")
                    records = diagnostic_records((run / item["log_path"]).read_text())
                    require(not any(x["severity"] == "error" for x in records), "success with compiler error")
                    # This immutable enrichment is distinct from the process receipt.
                    item = dict(item, olean_sha256=sha(obj), warning_count=sum(x["severity"] == "warning" for x in records),
                                source_option_directives=re.findall(r"set_option\s+\w+(?:\.\w+)*\s+[^\n]+", src.read_text()))
                    atomic_json(run / "attempts" / (item["attempt_id"] + ".validated.json"), item, exclusive=True)
                    # The index commits the enriched bytes; resume reads this record.
                    receipts[-1] = item
                record_status(run, "running" if item["status"] == "completed" else item["status"], context_hash, receipts)
                if item["status"] != "completed": return 2
                completed[module] = item
                if args.stop_after and len(completed) >= args.stop_after and len(completed) < len(order):
                    record_status(run, "checkpoint", context_hash, receipts); print(run); return 0
            audit = []
            audit_module = policy.get("audit_module")
            require(audit_module is None or audit_module in completed, "policy audit module was not compiled")
            emitting_modules = set()
            for module, item in completed.items():
                if audit_module is not None and module != audit_module:
                    continue
                for diagnostic in diagnostic_records((run / item["log_path"]).read_text()):
                    data = diagnostic.get("data", "")
                    if data.startswith("ERDOS20_AXIOM_AUDIT "):
                        emitting_modules.add(module)
                        audit.append(json.loads(data.removeprefix("ERDOS20_AXIOM_AUDIT ")))
            require(len(emitting_modules) == 1, "select one exact authoritative audit module in policy")
            inventory = strict_json(root / "evidence/axiom_audit_inventory.json")
            roots = {name for m in inventory["modules"] for name in m["roots"]}
            require(roots and len(audit) == len(roots) and {x["root"] for x in audit} == roots, "axiom root coverage mismatch")
            require(all(x["status"] == "pass" and set(x["axioms"]) <= ALLOWED_AXIOMS for x in audit), "axiom policy failure")
            for fixture in fixtures:
                charged = sum(item["wall_seconds"] for item in receipts)
                require(charged < args.wall_budget, "negative-control wall budget exhausted")
                src = contained(root, fixture["path"])
                require(sha(src) == manifest[fixture["path"]], "negative source drift before compiler")
                item = execute_attempt(run, [str(lean), "--json", *policy["lean_options"], str(src)], root, env,
                    {"kind": "negative", "fixture": fixture["path"], "source_sha256": sha(src)},
                    min(args.module_timeout, args.wall_budget-charged), args.max_log_bytes)
                receipts.append(item)
                require(sha(src) == manifest[fixture["path"]], "negative source drift during compiler")
                good = item["status"] == "failed" and negative_matches(diagnostic_records((run / item["log_path"]).read_text()), fixture, root, item["exit_code"])
                record_status(run, "running" if good else "negative_control_failed", context_hash, receipts)
                require(good, "negative fixture did not fail at intended target for intended reason: " + fixture["path"])
            # Recheck persistent source/cache/compiler drift before issuing completion.
            # This is local integrity checking, not defense against a malicious writer
            # capable of changing and restoring bytes between observations.
            verify_manifest(root, args.expected_manifest_sha256, policy["metadata_files"])
            final_environment, final_paths = verify_environment(root, lean, packages, policy)
            require(final_environment == environment and final_paths == dep_paths, "environment drift during replay")
            status = record_status(run, "completed", context_hash, receipts, module_count=len(order), root_count=len(roots), negative_count=len(fixtures), assurance="same-host project-source replay with pinned reused dependency cache; not independent reproduction")
            atomic_json(run / "completion.json", status, exclusive=True)
            print(run); return 0
        except BaseException as exc:
            record_status(run, "interrupted" if isinstance(exc, KeyboardInterrupt) else "failed", context_hash, receipts,
                          error_type=type(exc).__name__, error=str(exc)[:1000])
            raise


def verify_release(root, path, expected_sha):
    require(DIGEST.fullmatch(expected_sha) and sha(path) == expected_sha, "external release commitment mismatch")
    release = strict_json(path)
    require(release.get("schema") == "erdos20-release-commitment/1", "release schema mismatch")
    files = release.get("files")
    require(isinstance(files, dict) and files, "release file list empty")
    for name, digest in files.items():
        require(isinstance(digest, str) and DIGEST.fullmatch(digest), "invalid release digest")
        require(sha(contained(root, name)) == digest, "release artifact mismatch: " + name)
    return {"status": "release-bytes-checked", "artifact_count": len(files), "authenticated_origin": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    run = sub.add_parser("replay")
    run.add_argument("--root", type=Path, required=True); run.add_argument("--policy", type=Path, required=True)
    run.add_argument("--expected-policy-sha256", required=True); run.add_argument("--expected-manifest-sha256", required=True)
    run.add_argument("--lean", type=Path); run.add_argument("--packages", type=Path)
    run.add_argument("--runs", type=Path, default=Path("replay-runs")); run.add_argument("--resume")
    run.add_argument("--check-only", action="store_true"); run.add_argument("--stop-after", type=int)
    run.add_argument("--module-timeout", type=float, default=600); run.add_argument("--wall-budget", type=float, default=3600)
    run.add_argument("--max-log-bytes", type=int, default=16*1024*1024)
    rel = sub.add_parser("verify-release"); rel.add_argument("--root", type=Path, required=True)
    rel.add_argument("--release", type=Path, required=True); rel.add_argument("--expected-release-sha256", required=True)
    args = parser.parse_args()
    if args.action == "verify-release":
        print(json.dumps(verify_release(args.root.resolve(), args.release, args.expected_release_sha256))); return 0
    require(math.isfinite(args.module_timeout) and math.isfinite(args.wall_budget) and args.module_timeout > 0
            and args.wall_budget > 0 and args.max_log_bytes > 0, "resource bounds must be finite and positive")
    require(args.stop_after is None or args.stop_after > 0, "stop-after must be positive")
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt()))
    return replay(args)


if __name__ == "__main__":
    try: sys.exit(main())
    except (ReplayError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print("REPLAY_REJECTED: " + str(error), file=sys.stderr); sys.exit(2)
