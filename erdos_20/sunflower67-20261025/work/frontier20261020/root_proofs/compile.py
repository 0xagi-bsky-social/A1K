import pathlib, json, os, sys, subprocess, time, hashlib

root = pathlib.Path(__file__).resolve().parent
old = root.parents[1] / "frontier20261019"
cfg = json.loads((old / "runtime.json").read_text())
cwd = root.parents[2]
base = cwd / "outputs/frontier20261019/formal/source-rebuild-receipt/base-build"
cache = pathlib.Path("/home/user/Documents/Codex/2026-09-22/you-ve-been-interrupted-unexpectedly-please/work/erdos20-v13/lean/.lake/build/lib/lean")
env = dict(os.environ)
env["LEAN_PATH"] = ":".join(map(str, [root / "build", cache, base, *cfg["package_paths"]]))
name = sys.argv[1]
source = root / name
start = time.monotonic()
before = source.read_bytes()
command = [cfg["lean"], "--memory=768", "--threads=1", "-o", str(root / "build" / source.with_suffix(".olean").name), name]
attempt = str(time.time_ns())
(root / "receipts" / (source.stem + "." + attempt + ".started.json")).write_text(
    json.dumps({"source_sha256":hashlib.sha256(before).hexdigest(),"command":command,"status":"started"},indent=2))
try:
    proc = subprocess.run(command, cwd=root, env=env, text=True, capture_output=True, timeout=100)
    code, output = proc.returncode, proc.stdout + proc.stderr
except subprocess.TimeoutExpired as exc:
    code = 124
    output = "RESOURCE LIMIT: 100-second subprocess timeout\n"
    for v in (exc.stdout, exc.stderr):
        if v: output += v.decode(errors="replace") if isinstance(v, bytes) else v
rec = {
    "source": str(source), "source_sha256": hashlib.sha256(before).hexdigest(),
    "source_stable": before == source.read_bytes(), "command": command,
    "LEAN_PATH": env["LEAN_PATH"], "exit_code": code,
    "elapsed_seconds": time.monotonic() - start,
    "output": output,
    "output_sha256": hashlib.sha256(output.encode()).hexdigest(),
    "assurance": "elaborated" if code == 0 else "draft",
    "limits": "Same evaluator; pinned Lean and dependency caches; this is not a clean independent replay."
}
(root / "receipts" / (source.stem + ".json")).write_text(json.dumps(rec, indent=2))
(root / "receipts" / (source.stem + "." + attempt + ".json")).write_text(json.dumps(rec, indent=2))
print(output)
print("EXIT", code, "SECONDS", rec["elapsed_seconds"])
sys.exit(code)
