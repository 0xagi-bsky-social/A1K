#!/usr/bin/env python3
"""Prepare the named P9-Q8 internal DAG and optional explicit v9 exterior lists.

Standard library only; no producer import, model, solver or coefficient replay.
This source was prepared without executing it. Missing replays remain pending
paths; only the separate literal stage checker can certify their coverage.
"""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUT = HERE / 'degree17_full'
V4 = 'a1beae56f60205a48442a1c6a31d2148557443511fb119a1936ffda8578bebf2'
V6 = '8f43465ef15e09ba5ea8f472a4382f844ccb3ebeface8841f7963625f65e8138'
V8 = 'c7cf58b6d2bc9e523d729dbc5a2ae9aeb83164fabed3b4b1211b30d6e889f245'
V9 = '31368d8392328daa9f161b23e40ef7c3df3d9acd4743cf4914f9df0215b74eb2'
Y_MANIFEST = 'fadd92fe79c991abd67629e421baea45a73567adefd692c65c3bfbf1e2b8cba7'
# This fixed list records proof ancestry, never a newest-file glob policy.
INTERNALS = (
    ('IZ01', 0, V4, '1598841bf84b', '0df5e130bf938b72c88c1854142d6b36fa38a161aaa0f7432fc27dad218cc9ea', ()),
    ('IZ03', 0, V4, '5886d0eeef0c', '6878b76cbd74036e489a428c60fd13d9438becaa6586bd9ed188f6b58aadd152', ()),
    ('IZ05', 0, V4, 'a95ee639bcb8', '7254b16ca1b6c74c80afce8b914b2972481f8b3ae81d9acbd02ccc224696fd2a', ()),
    ('IZ07', 0, V4, 'add27f952618', 'e7a8612c0b9abb1460988b7578ac1950b114cfa9aaef516e46bfe659dd0b3aea', ()),
    ('IZ00', 2, V6, '68436e5cbfa8', 'e7cd4d0524b9efb2934bead97869aa3d51984714183ef91b52da9d0061c030f4', ('IZ01','IZ03','IZ05','IZ07')),
    ('IZ02', 3, V6, 'dbfb7ca495e1', '21340f7bf930aa430cfb979c5e0e3823b5a33e3b0a38d88e092a551f0fce8368', ('IZ01','IZ03','IZ05','IZ07','IZ00')),
    ('IZ06', 3, V8, '38a3b9ba779e-phaseone', '91db0f39a36148877cd8b2836130c977a2d943be2f649d260b1c4e7d4094bd83', ('IZ01','IZ03','IZ05','IZ07','IZ00')),
    ('IZ04', 4, V9, 'cba75ba7b396', 'a761d6eb9c04357cfbfc6f06f9bc59ace8b0e0d191c30387bd09103ac15c6204', ('IZ01','IZ03','IZ05','IZ07','IZ00','IZ02','IZ06')),
)
Z_ORBITS = {
    'IZ00': [960,1472,1728], 'IZ01': [1856,1920],
    'IZ02': [2496,2752,3264,4544,4800,5312],
    'IZ03': [2880,2944,3392,3456,3648,3712,4928,4992,5440,5504,5696,5760],
    'IZ04': [3840,5888], 'IZ05': [6336],
    'IZ06': [6464,6528,6720,6784,7232,7296], 'IZ07': [6912,7424,7680],
}


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def strict(data):
    dual = data.get('dual', {})
    zero = data.get('certificate_kind') == 'zero-infeasibility'
    integers = [dual.get(k) for k in ('scale','H','correction','upper_numerator')]
    return (data.get('status') == 0 and all(type(v) is int for v in integers)
            and integers[0] > 0 and integers[3] == integers[1] + integers[2]
            and integers[3] < (0 if zero else 51 * integers[0])
            and dual.get('below0' if zero else 'below51') is True)


def prepare(e4_path=None, e3_path=None):
    tracked, nodes, unproved = {}, [], []

    def read(path, expected=None):
        path = Path(path).resolve()
        digest = sha(path)
        require(expected is None or digest == expected, 'Changed named input: ' + str(path))
        require(path not in tracked or tracked[path] == digest, 'Input changed during preparation')
        tracked[path] = digest
        return json.loads(path.read_text())

    def add(nid, path, digest, uses, replay=None):
        path = Path(path).resolve()
        d = read(path, digest)
        require(d.get('kind') == 'P9-Q8' and strict(d), 'Leaf is not a strict Q8 diagnostic')
        rp = (HERE / 'degree17_full_replay' / (path.stem + '-replay.json')).resolve()
        node = dict(id=nid, receipt=str(path), receipt_sha256=digest,
                    replay=str(rp), uses=list(uses))
        if replay is not None:
            require(Path(replay['path']).resolve() == rp, 'Unexpected explicit replay path')
            read(rp, replay['sha256'])
            node['replay_sha256'] = replay['sha256']
        elif rp.is_file():
            node['replay_sha256'] = sha(rp)
        nodes.append(node)
        return d

    manifest = read(OUT / 'P9-IY-active-v2-replayed-manifest.json', Y_MANIFEST)
    require(manifest.get('exact_replays_bound') is True, 'Unreplayed Y manifest')
    yrows = [r for r in manifest['records'] if r['kind'] == 'P9-Q8']
    require({r['case'] for r in yrows} == {'IY00','IY01','IY02','IY03'}
            and len(yrows) == 4, 'Incomplete named Q8-side Y stage')
    yids, yzero = [], set()
    for r in sorted(yrows, key=lambda r:r['case']):
        nid = 'Y-' + r['case']
        add(nid, r['receipt']['path'], r['receipt']['sha256'], [], r['exact_replay'])
        yids.append(nid)
        yzero.update(r['orbit'])
    require(len(yzero) == 15, 'Wrong initial Y domain')
    for case, stage, source, suffix, digest, predecessors in INTERNALS:
        version = {V4:4,V6:6,V8:8,V9:9}[source]
        name = f'P9-Q8-{case}-internal-Z-stage{stage}-v{version}-{suffix}.json'
        d = add('Z-' + case, OUT / name, digest,
                yids + ['Z-' + c for c in predecessors])
        expected = yzero | {s for c in predecessors for s in Z_ORBITS[c]}
        require(d['source_sha256'] == source and d['case'] == case
                and set(d['forbidden']) == expected and len(d['forbidden']) == len(expected)
                and not d['empty_z'] and d['assigned_z'] is None
                and not d['forbid_four_core'] and not d.get('extra_members')
                and d.get('h27_cliques') is None,
                'Named internal leaf has different stage premises')
    internal_ids = [n['id'] for n in nodes]
    four_ids = []

    def exterior(progress_path, stage, uses):
        progress = read(progress_path)
        require(progress.get('kind') == 'P9-Q8' and progress.get('stage') == stage
                and progress.get('source_sha256') == V9
                and len(progress.get('records', [])) == progress.get('completed'),
                'Wrong or inconsistent named exterior progress')
        seen = set()
        for item in progress['records']:
            case = item['case']
            require(case.startswith(stage + '_') and case not in seen, 'Duplicate or wrong exterior case')
            seen.add(case)
            d = read(item['path'], item['sha256'])
            require(d.get('kind') == 'P9-Q8' and d.get('source_sha256') == V9
                    and d.get('case') == case and d.get('empty_z') is True
                    and d.get('assigned_z') is None and set(d.get('forbidden', [])) == yzero
                    and d.get('forbid_four_core') == (stage == 'E3')
                    and d.get('extra_members') == [] and d.get('h27_cliques') is None,
                    'Exterior receipt has unexpected literal premises')
            nid = ('four-' if stage == 'E4' else 'three-') + case
            if strict(d):
                add(nid, item['path'], item['sha256'], uses)
                if stage == 'E4':
                    four_ids.append(nid)
            else:
                unproved.append(dict(case=case, receipt=str(Path(item['path']).resolve()),
                                     receipt_sha256=item['sha256']))
        return progress

    if e4_path is not None:
        exterior(e4_path, 'E4', internal_ids)
    if e3_path is not None:
        require(e4_path is not None, 'E3 requires an explicitly named E4 list')
        exterior(e3_path, 'E3', internal_ids + four_ids)
    for path, digest in tracked.items():
        require(sha(path) == digest, 'Input changed during preparation')
    receipt_paths = {Path(n['receipt']) for n in nodes}
    return dict(schema='d17-stage-proof-plan-v1', kind='P9-Q8', nodes=nodes,
                unproved_candidates=unproved,
                construction_inputs=[dict(path=str(p), sha256=h) for p,h in tracked.items()
                                     if p not in receipt_paths])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--e4-progress', type=Path)
    parser.add_argument('--e3-progress', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    require(not args.output.exists(), 'Refusing to overwrite an explicit plan')
    plan = prepare(args.e4_progress, args.e3_progress)
    with args.output.open('x') as handle:
        json.dump(plan, handle, indent=2, allow_nan=False)
        handle.write('\n')
    print(json.dumps(dict(status='PREPARED_EXPLICIT_Q8_PLAN_NOT_VALIDATED',
                          nodes=len(plan['nodes']), unproved=len(plan['unproved_candidates']),
                          output=str(args.output.resolve()))))


if __name__ == '__main__':
    main()
