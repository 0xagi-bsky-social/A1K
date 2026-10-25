#!/usr/bin/env python3
"""Resume the explicit 123-leaf D18 P10 arithmetic replay, serially.

Run with the existing SciPy Python and OPENBLAS_NUM_THREADS=1. Completed
hash-matched strict PASS receipts are reused. No solver is invoked. This
driver does not validate the ordinary model bridge or replace the independent
coverage checker. A stale/failing existing receipt is preserved and rejected.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
MANIFEST_SHA = '41a906f71782390491b7e4ee001f5f97541703f593bad4403b4be2f10d9578df'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest_path = HERE / 'D18-P10-active-manifest.json'
    manifest_bytes = manifest_path.read_bytes()
    if hashlib.sha256(manifest_bytes).hexdigest() != MANIFEST_SHA:
        raise ValueError('Active manifest differs from the checked 123-leaf chain')
    manifest = json.loads(manifest_bytes)
    entries = [entry for stage in manifest['stages'] for entry in stage['receipts']]
    if len(entries) != 123 or len({e['path'] for e in entries}) != 123:
        raise ValueError('Unexpected active leaf count or duplicate receipt')
    records = []
    replayer = HERE / 'replay_degree18_p10.py'
    for completed, entry in enumerate(entries, 1):
        path = HERE / entry['path']
        if sha(path) != entry['sha256']:
            raise ValueError(f'Changed active receipt: {path}')
        output = HERE / 'degree18_p10_replay' / (path.stem + '-replay.json')
        if not output.exists():
            subprocess.run([sys.executable, str(replayer), '--receipt', str(path),
                            '--seconds', '30'], check=True)
        result = json.loads(output.read_text())
        if not (result['result'] == 'PASS'
                and result['receipt_sha256'] == sha(path)
                and result['replayer_sha256'] == sha(replayer)
                and result['exact_replay']['strict_exclusion']):
            raise ValueError(f'Existing replay is stale or not a strict PASS: {output}')
        records.append(dict(receipt=str(path), receipt_sha256=sha(path),
                            replay=str(output), replay_sha256=sha(output), result='PASS'))
        progress = HERE / 'degree18_p10/active-replay-progress.json'
        progress.write_text(json.dumps(dict(completed=completed, total=123,
                                           last=path.name, all_completed_pass=True), indent=2) + '\n')
    if manifest_path.read_bytes() != manifest_bytes:
        raise ValueError('Manifest changed during replay')
    index = HERE / 'degree18_p10/complete-replay-index.json'
    index.write_text(json.dumps(dict(manifest_sha256=MANIFEST_SHA,
                                    replayer_sha256=sha(replayer), count=123, all_pass=True,
                                    assurance='Shared-producer exact integer arithmetic and dependency replay; ordinary bridge and independent orbit coverage remain separate. Not Lean or final review.',
                                    records=records), indent=2) + '\n')
    print(json.dumps(dict(COMPLETE=123, all_pass=True, index=str(index))), flush=True)


if __name__ == '__main__':
    main()
