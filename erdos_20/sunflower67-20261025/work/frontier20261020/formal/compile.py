import pathlib, json, os, sys, subprocess, time, hashlib

root = pathlib.Path(__file__).resolve().parent
old = root.parents[1] / "frontier20261019"
cfg = json.loads((old / "runtime.json").read_text())
cwd = root.parents[2]
base = cwd / "outputs/frontier20261019/formal/source-rebuild-receipt/base-build"
cache = pathlib.Path("/home/user/Documents/Codex/2026-09-22/you-ve-been-interrupted-unexpectedly-please/work/erdos20-v13/lean/.lake/build/lib/lean")
env = dict(os.environ)
env["LEAN_PATH"] = ":".join(map(str, [root / "build", root.parent / "theory/build", cache, base, *cfg["package_paths"]]))
name = sys.argv[1]
source = root / name
start = time.monotonic()
before = source.read_bytes()
command = [cfg["lean"], "--memory=1024", "-o", str(root / "build" / source.with_suffix(".olean").name), name]
proc = subprocess.run(command, cwd=root, env=env, text=True, capture_output=True, timeout=120)
rec = {
    "source": str(source), "source_sha256": hashlib.sha256(before).hexdigest(),
    "source_stable": before == source.read_bytes(), "command": command,
    "LEAN_PATH": env["LEAN_PATH"], "exit_code": proc.returncode,
    "elapsed_seconds": time.monotonic() - start,
    "output": proc.stdout + proc.stderr,
    "output_sha256": hashlib.sha256((proc.stdout + proc.stderr).encode()).hexdigest(),
    "assurance": "elaborated" if proc.returncode == 0 else "draft",
    "limits": "Same evaluator; pinned Lean and dependency caches; this is not a clean independent replay."
}
(root / "receipts" / (source.stem + ".json")).write_text(json.dumps(rec, indent=2))
(root / "receipts" / (source.stem + "." + str(time.time_ns()) + ".json")).write_text(json.dumps(rec, indent=2))
print(proc.stdout + proc.stderr)
print("EXIT", proc.returncode, "SECONDS", rec["elapsed_seconds"])
sys.exit(proc.returncode)
