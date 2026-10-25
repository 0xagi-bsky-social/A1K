#!/usr/bin/env python3
"""Prepare an explicit D17 proof plan from named, complete discovery lists.

Standard library only. Does not choose files by glob, import a producer, trust
its orbit counts, run a model or replay, or assert closure. Exact replay paths
are recorded explicitly; missing replays cause the separate validator to fail.
"""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def prepare(e4_path, e3_path=None):
    tracked = {}

    def read(path, expected=None):
        path = Path(path).resolve()
        digest = sha(path)
        require(expected is None or digest == expected, 'Input hash mismatch: ' + str(path))
        require(path not in tracked or tracked[path] == digest, 'Input changed during preparation')
        tracked[path] = digest
        return json.loads(path.read_text())

    e4_path = e4_path.resolve()
    e4 = read(e4_path)
    require(e4.get('stage') == 'E4' and e4.get('completed') == e4.get('total')
            and len(e4.get('records', [])) == e4['total'],
            'The named E4 discovery list is incomplete')
    kind = e4['kind']
    require(kind in [f'P10-H{i}' for i in range(1, 7)] + ['P9-P8-i1', 'P9-P8-i2'],
            'This list adapter supports the eight run_d17_exterior_stage kinds')
    nodes, unproved = [], []
    ids = set()

    def add(nid, item, uses, explicit_replay=None):
        require(nid not in ids, 'Duplicate node ID')
        ids.add(nid)
        path = Path(item['path']).resolve()
        data = read(path, item['sha256'])
        require(data.get('kind') == kind, 'Leaf belongs to another root geometry')
        replay_path = (HERE / 'degree17_full_replay' / (path.stem + '-replay.json')).resolve()
        node = dict(id=nid, receipt=str(path), receipt_sha256=item['sha256'],
                    replay=str(replay_path), uses=uses)
        if explicit_replay is not None:
            require(Path(explicit_replay['path']).resolve() == replay_path, 'Unexpected explicit replay path')
            node['replay_sha256'] = explicit_replay['sha256']
        elif replay_path.is_file():
            node['replay_sha256'] = sha(replay_path)
        nodes.append(node)
        return data

    def add_exterior(nid, item, uses):
        data = read(item['path'], item['sha256'])
        dual = data.get('dual', {})
        scale, numerator = dual.get('scale'), dual.get('upper_numerator')
        target = 0 if data.get('certificate_kind') == 'zero-infeasibility' else 51 * scale if type(scale) is int else None
        if (data.get('status') == 0 and type(scale) is int and scale > 0
                and type(numerator) is int and numerator < target):
            add(nid, item, uses)
            return True
        unproved.append(dict(case=item['case'], receipt=str(Path(item['path']).resolve()),
                             receipt_sha256=item['sha256']))
        return False

    iy_ids = []
    yprior = e4.get('Y_antecedent')
    if kind.startswith('P9-'):
        require(isinstance(yprior, dict), 'P9 discovery list lacks its explicit Y antecedent')
        manifest = read(yprior['path'], yprior['sha256'])
        require(manifest.get('exact_replays_bound') is True, 'Y manifest is not the completed exact binding')
        for record in manifest['records']:
            if record['kind'] != kind:
                continue
            nid = 'Y-' + record['case']
            add(nid, record['receipt'], [], record['exact_replay'])
            iy_ids.append(nid)
        require(len(iy_ids) == 4, 'P9 list adapter expects its four explicit IY entries')
    else:
        require(yprior is None, 'P10 must use the separate component summary')
    internals = e4.get('internal_antecedents')
    require(isinstance(internals, list) and internals, 'Missing explicit internal antecedents')
    stage0 = [r for r in internals if r.get('stage') == 0]
    stage1 = [r for r in internals if r.get('stage') == 1]
    require(len(stage0) + len(stage1) == len(internals), 'Only this driver\'s stages0/1 are supported')
    zero_ids = ['Z0-' + r['case'] for r in stage0]
    for item, nid in zip(stage0, zero_ids):
        add(nid, item, list(iy_ids))
    one_ids = ['Z1-' + r['case'] for r in stage1]
    for item, nid in zip(stage1, one_ids):
        add(nid, item, iy_ids + zero_ids)
    all_internal_ids = iy_ids + zero_ids + one_ids
    four_ids = []
    for record in e4['records']:
        nid = 'four-' + record['case']
        if add_exterior(nid, record, list(all_internal_ids)):
            four_ids.append(nid)
    if e3_path is not None:
        e3 = read(e3_path)
        require(e3.get('kind') == kind and e3.get('stage') == 'E3'
                and e3.get('completed') == e3.get('total')
                and len(e3.get('records', [])) == e3['total'],
                'The named E3 discovery list is incomplete')
        previous = e3.get('four_core_antecedent', {})
        require(Path(previous.get('path', '')).resolve() == e4_path
                and previous.get('sha256') == tracked[e4_path]
                and e3.get('Y_antecedent') == yprior
                and e3.get('internal_antecedents') == internals,
                'E3 does not bind the explicitly supplied E4 stage and antecedents')
        for record in e3['records']:
            add_exterior('three-' + record['case'], record, list(four_ids))
    for path, digest in tracked.items():
        require(sha(path) == digest, 'Input changed during preparation')
    plan = dict(schema='d17-stage-proof-plan-v1', kind=kind, nodes=nodes,
                unproved_candidates=unproved,
                construction_inputs=[dict(path=str(path), sha256=digest)
                                     for path, digest in tracked.items() if path not in
                                     {Path(n['receipt']) for n in nodes}])
    if kind.startswith('P10-'):
        plan['p10_internal_summary'] = str(HERE / 'degree17-replay/P10-nonempty-summary.json')
    return plan


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--e4-progress', type=Path, required=True)
    parser.add_argument('--e3-progress', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    require(not args.output.exists(), 'Refusing to overwrite an explicit proof plan')
    plan = prepare(args.e4_progress, args.e3_progress)
    with args.output.open('x') as handle:
        json.dump(plan, handle, indent=2, allow_nan=False)
        handle.write('\n')
    print(json.dumps(dict(status='PREPARED_EXPLICIT_PLAN_NOT_VALIDATED', kind=plan['kind'],
                          nodes=len(plan['nodes']), unproved_candidates=[r['case'] for r in plan['unproved_candidates']],
                          output=str(args.output.resolve()))))


if __name__ == '__main__':
    main()
