"""Sequential bounded recovery runner; never rebuild a successful unchanged input."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

p = Path(__file__).resolve().parent
root = p.parents[2]
runtime = json.loads((root / 'work/frontier20261019/runtime.json').read_text())
module = sys.argv[1]
source = p / (module + '.lean')
target = p / 'build' / (module + '.olean')
receipt_path = p / 'receipts' / (module + '.json')
source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
if receipt_path.exists():
    old = json.loads(receipt_path.read_text())
    if old['exit_code'] == 0 and old['source_sha256'] == source_hash and target.exists():
        print(json.dumps({'module': module, 'status': 'reused-unchanged-success'}))
        sys.exit(0)

env = os.environ.copy()
env['LEAN_PATH'] = ':'.join([str(p / 'build'),
    str(root / 'work/frontier20261020/closure-rebuild/build'), *runtime['package_paths']])
command = [runtime['lean'], '-j1', '-M512', '-o', str(target), str(source)]
start = time.monotonic()
timed_out = False
with (p / 'receipts' / (module + '.log')).open('w') as log:
    try:
        proc = subprocess.run(command, env=env, cwd=root, text=True,
            stdout=log, stderr=subprocess.STDOUT, timeout=120)
        code = proc.returncode
    except subprocess.TimeoutExpired:
        timed_out = True
        code = 124
log_path = p / 'receipts' / (module + '.log')
receipt = {
    'module': module, 'exit_code': code, 'timed_out': timed_out,
    'elapsed_seconds': round(time.monotonic() - start, 3),
    'source_sha256': source_hash,
    'object_sha256': hashlib.sha256(target.read_bytes()).hexdigest() if target.exists() and code == 0 else None,
    'output_sha256': hashlib.sha256(log_path.read_bytes()).hexdigest(),
    'lean': runtime['lean'],
    'lean_version_observed': subprocess.check_output([runtime['lean'], '--version'], text=True).strip(),
    'lean_path': env['LEAN_PATH'], 'command': command,
    'limits': {'lean_memory_MiB': 512, 'workers': 1, 'timeout_seconds': 120},
    'evaluator': 'current-agent; no independent evaluator',
    'grade': 'elaborated' if code == 0 else 'draft'
}
receipt_path.write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({k: receipt[k] for k in ['module', 'exit_code', 'timed_out', 'elapsed_seconds', 'source_sha256']}))
if code:
    print(log_path.read_text()[-6000:])
sys.exit(code)
