#!/usr/bin/env python3
"""Resume exact arithmetic for an explicit D17 plan, one fresh process per leaf.

The separate marker-stage validator establishes coverage. This driver never
calls a solver and never upgrades a missing, stale, or failed replay to PASS.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPLAYER_SHA = '884b1bd4c06e044c3480b4cbf9ad27cd68bb2102b626ea745a4eb2ac055483f3'
KNOWN_REPLAYERS = {
    '3ac2265ad2fd090bf2b06e012ed8c9551f6e7e3bb9d0d7f903fb7d3a756a937b',
    '2e2238bfeb0ba50b98e74d4fe672ed58ee54d017b9a7387da15d875728863824',
    '024c11d4897818233a74b7fff9f3c925ea521dd52818ec16411bd98ec3650b44',
    REPLAYER_SHA,
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(value, message):
    if not value:
        raise ValueError(message)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('plan', type=Path)
    args = ap.parse_args()
    raw = args.plan.read_bytes()
    plan_hash = hashlib.sha256(raw).hexdigest()
    plan = json.loads(raw)
    require(plan['schema'] == 'd17-stage-proof-plan-v1', 'Unknown plan schema')
    require(not plan.get('unproved_candidates'), 'Plan has unproved candidates')
    replayer = HERE / 'replay_degree17_full_v6.py'
    require(sha(replayer) == REPLAYER_SHA, 'Frozen replayer changed')
    nodes = plan['nodes']
    require(len({n['receipt'] for n in nodes}) == len(nodes), 'Duplicate leaf receipt')
    progress = args.plan.with_name(args.plan.stem + '-replay-progress.json')
    index = args.plan.with_name(args.plan.stem + '-replay-index.json')
    require(not index.exists(), 'Completed index already exists; inspect it instead')
    records = []
    env = dict(os.environ, OPENBLAS_NUM_THREADS='1', PYTHONDONTWRITEBYTECODE='1')
    for number, node in enumerate(nodes, 1):
        receipt = Path(node['receipt'])
        expected = node['receipt_sha256']
        require(sha(receipt) == expected, 'Changed planned receipt')
        output = Path(node['replay'])
        require(output.resolve() == (HERE / 'degree17_full_replay' /
                (receipt.stem + '-replay.json')).resolve(), 'Unexpected replay path')
        reused = output.exists()
        if not reused:
            subprocess.run([sys.executable, str(replayer), '--receipt', str(receipt),
                            '--source', 'auto', '--seconds', '30'],
                           check=True, timeout=45, env=env)
        result = json.loads(output.read_text())
        original = json.loads(receipt.read_text())
        require(result.get('result') == 'PASS'
                and result.get('all_inputs_unchanged') is True
                and result.get('receipt_sha256') == expected
                and result.get('replayer_sha256') in KNOWN_REPLAYERS
                and result.get('source', {}).get('sha256') == original['source_sha256']
                and result.get('premise_sha256') == original['premise_sha256']
                and result.get('exact_replay', {}).get('strict_exclusion') is True,
                'Missing, stale, or nonstrict exact replay: ' + str(output))
        if 'replay_sha256' in node:
            require(sha(output) == node['replay_sha256'], 'Changed pre-existing replay')
        records.append(dict(id=node['id'], receipt=str(receipt), receipt_sha256=expected,
                            replay=str(output), replay_sha256=sha(output), result='PASS'))
        state = dict(plan=str(args.plan.resolve()), plan_sha256=plan_hash,
                     completed=number, total=len(nodes), last=node['id'],
                     all_completed_pass=True)
        progress.write_text(json.dumps(state, indent=2) + '\n')
        print(json.dumps(dict(completed=number, total=len(nodes), id=node['id'],
                              reused=reused)), flush=True)
    require(args.plan.read_bytes() == raw, 'Plan changed during replay')
    require(sha(replayer) == REPLAYER_SHA, 'Replayer changed during replay')
    with index.open('x') as handle:
        json.dump(dict(plan_sha256=plan_hash, count=len(records), all_pass=True,
                       records=records,
                       assurance='Shared-producer exact integer arithmetic replay. '
                       'Independent stage coverage and ordinary bridges remain separate. '
                       'Not Lean or final review.'), handle, indent=2)
        handle.write('\n')
    print(json.dumps(dict(complete=True, index=str(index), leaves=len(records))), flush=True)


if __name__ == '__main__':
    main()
