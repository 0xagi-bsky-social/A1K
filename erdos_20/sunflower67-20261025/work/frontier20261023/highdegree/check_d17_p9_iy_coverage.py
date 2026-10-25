#!/usr/bin/env python3
"""Independent small P9-internal orbit census and immutable twelve-case manifest.

Uses only Python's standard library; imports no model, numerical package or
upstream checker. The finite domain is S6 and the fifteen four-subsets of six
points, plus the forty-five pairs of P10 blocks. No LP/model build or exact
dual replay occurs. --bind-replays additionally binds twelve already completed
full-model exact replays; it does not execute them. Deadline: ten seconds.
"""
import argparse
import hashlib
import itertools as it
import json
from pathlib import Path
import signal
import time

HERE = Path(__file__).resolve().parent
SOURCE_SHA256 = '497f71f4fdf555c7456b42123684e7fd5059769f89662c257e2263425798b31a'
REPLAYER_SHA256 = '3ac2265ad2fd090bf2b06e012ed8c9551f6e7e3bb9d0d7f903fb7d3a756a937b'
KINDS = ('P9-P8-i1', 'P9-P8-i2', 'P9-Q8')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def mask(block):
    return sum(1 << v for v in block)


def value_hash(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'),
                                     allow_nan=False).encode()).hexdigest()


def reconstruct():
    p10 = frozenset(frozenset(map(int, text)) for text in
                   '012 015 023 034 045 124 134 135 235 245'.split())
    p9 = p10 - {frozenset((0, 1, 2))}
    aut10, aut9 = [], []
    for perm in it.permutations(range(6)):
        def image(family):
            return frozenset(frozenset(perm[v] for v in block) for block in family)
        if image(p10) == p10:
            aut10.append(perm)
        if image(p9) == p9:
            aut9.append(perm)
    require(len(aut10) == 60 and len(aut9) == 6, 'Unexpected full automorphism orders')
    quads = {frozenset(vs) for vs in it.combinations(range(6), 4)}
    unseen, records = set(quads), []
    while unseen:
        rep = min(unseen, key=mask)
        orbit = {frozenset(perm[v] for v in rep) for perm in aut9}
        require(orbit <= unseen, 'Internal orbits overlap or leave their domain')
        records.append(dict(case=f'IY{len(records):02d}', marker=mask(rep),
                            points=sorted(rep), orbit=sorted(map(mask, orbit))))
        unseen -= orbit
    require([len(r['orbit']) for r in records] == [3, 3, 6, 3]
            and set().union(*(set(r['orbit']) for r in records)) == set(map(mask, quads)),
            'Internal orbits fail to partition all fifteen four-sets')
    all_pairs = {frozenset(pair) for pair in it.combinations(p10, 2)}
    unseen, opposite, deletion_orbits = set(all_pairs), {}, {}
    while unseen:
        rep = min(unseen, key=lambda pair: tuple(sorted(map(mask, pair))))
        orbit = {frozenset(frozenset(perm[v] for v in block) for block in rep) for perm in aut10}
        require(orbit <= unseen, 'P8 deletion orbits overlap or leave their domain')
        a, b = tuple(rep)
        name = f'P9-P8-i{len(a & b)}'
        require(name in KINDS and name not in opposite, 'Unexpected P8 deletion type')
        opposite[name] = sorted(mask({v + 6 for v in block}) for block in p10 - rep)
        deletion_orbits[name] = dict(omitted=sorted(map(mask, rep)), orbit_size=len(orbit))
        unseen -= orbit
    require(set(opposite) == set(KINDS[:2]) and sum(r['orbit_size'] for r in deletion_orbits.values()) == 45,
            'P8 deletion classification is incomplete')
    q8 = [frozenset((h, *ab)) for h in (0, 1) for ab in it.combinations((2, 3, 4), 2)]
    q8 += [frozenset((0, 1, 5)), frozenset((0, 1, 6))]
    opposite['P9-Q8'] = sorted(mask({v + 6 for v in block}) for block in q8)
    return sorted(map(mask, p9)), records, opposite, deletion_orbits


def check(bind_replays=False):
    started = time.monotonic()
    inputs = {}

    def bind(path, expected=None):
        path = Path(path).resolve()
        digest = sha(path)
        require(expected is None or digest == expected, f'Hash mismatch: {path}')
        require(path not in inputs or inputs[path] == digest, 'Input changed during inspection')
        inputs[path] = digest
        return dict(path=str(path), sha256=digest)

    source = bind(HERE / 'degree17_full_projection_v2.py', SOURCE_SHA256)
    checker = bind(__file__)
    ylink, orbits, opposite, deletion_orbits = reconstruct()
    files = sorted((HERE / 'degree17_full').glob('*IY*-internal-smoke-v2-*.json'))
    require(len(files) == 12, 'Expected precisely twelve active v2 IY receipts')
    seen, rows = set(), []
    for path in files:
        bound = bind(path)
        data = json.loads(path.read_text())
        kind, case = data.get('kind'), data.get('case')
        require(kind in KINDS and (kind, case) not in seen, 'Unexpected or duplicate kind/case')
        candidates = [r for r in orbits if r['case'] == case]
        require(len(candidates) == 1, 'Unknown IY orbit label')
        orbit = candidates[0]
        require(data.get('source_sha256') == SOURCE_SHA256 and data.get('status') == 0
                and data.get('target_residuals') == 51 and data.get('root_degree') == 17
                and data.get('point_cap') == 17 and data.get('mu') == 41, 'Wrong D17 source or scope')
        require(data.get('empty_z') is False and data.get('assigned_z') is None
                and data.get('forbidden') == [] and data.get('forbid_four_core') is False
                and data.get('crowding_imports') is True and type(data.get('degree_distributions')) is bool,
                'An extra mathematical branch restriction prevents full IY coverage')
        require(not data.get('P10_internal_exclusion_receipts'), 'P9 receipt imports P10 empty internals')
        g = data.get('geometry', {})
        require(g.get('kind') == kind and g.get('root') == 15 and g.get('Y') == list(range(6))
                and g.get('Z') == list(range(6, 13 if kind == 'P9-Q8' else 12))
                and g.get('excluded_Y_internal_count') == 0
                and sorted(g.get('link', [])) == sorted(ylink + opposite[kind]), 'Complete root geometry differs')
        require(g.get('automorphism_orders', {}).get('Y') == 6, 'P9 automorphism order differs')
        iy_records = {name: r for name, r in g.get('records', {}).items() if name.startswith('IY')}
        require(set(iy_records) == {r['case'] for r in orbits}, 'Incomplete recorded IY catalogue')
        for r in orbits:
            got = iy_records[r['case']]
            require(got == dict(marker=r['marker'], category='internal-Y', orbit_size=len(r['orbit']), orbit=r['orbit']),
                    'Producer IY orbit differs from independent set census')
        imports = data.get('imported_crowding_sources')
        require(isinstance(imports, dict) and imports, 'Missing mathematical dependency registry')
        for item in imports.values():
            require(isinstance(item, dict) and set(item) == {'path', 'sha256'}, 'Malformed dependency')
            bind(item['path'], item['sha256'])
        bind(HERE / 'D18-structural-tools.md', data.get('structural_note_sha256'))
        bind(HERE / 'D18-pool-research.md', data.get('pool_note_sha256'))
        local = HERE.parents[1] / 'frontier20261020/prior-art68/repository/companion/upstream/MU42/scripts/local43.py'
        bind(local, data.get('imported_local43_sha256'))
        identity = dict(source_sha256=SOURCE_SHA256,
                        imported_local43_sha256=data['imported_local43_sha256'],
                        structural_note_sha256=data['structural_note_sha256'],
                        pool_note_sha256=data['pool_note_sha256'], imported_crowding_sources=imports,
                        P10_internal_exclusion_receipts={}, kind=kind, literal_premises=data['literal_premises'])
        require(value_hash(identity) == data.get('premise_sha256'), 'Producer premise identity differs')
        dual = data.get('dual', {})
        require(all(type(dual.get(k)) is int for k in ('scale', 'H', 'correction', 'upper_numerator')),
                'Reported dual scalars must be integers')
        numerator, scale = dual['upper_numerator'], dual['scale']
        require(scale > 0 and numerator == dual['H'] + dual['correction']
                and numerator < 51 * scale and dual.get('below51') is True, 'Reported scalars are not strict below51')
        entry = dict(kind=kind, case=case, marker=orbit['marker'], orbit=orbit['orbit'], receipt=bound,
                     premise_sha256=data['premise_sha256'], reported_numerator=numerator, scale=scale,
                     reported_margin_numerator=51 * scale - numerator,
                     scalar_assurance='reported H/correction consistency only; coefficient replay is separate')
        if bind_replays:
            replay_path = HERE / 'degree17_full_replay' / (path.stem + '-replay.json')
            evidence_bound = bind(replay_path)
            evidence = json.loads(replay_path.read_text())
            exact = evidence.get('exact_replay', {})
            require(evidence.get('result') == 'PASS' and evidence.get('all_inputs_unchanged') is True
                    and evidence.get('receipt_sha256') == bound['sha256']
                    and evidence.get('replayer_sha256') == REPLAYER_SHA256
                    and evidence.get('source', {}).get('sha256') == SOURCE_SHA256
                    and evidence.get('premise_sha256') == data['premise_sha256']
                    and evidence.get('certificate_kind') == 'trace-upper-bound'
                    and exact.get('strict_exclusion') is True
                    and exact.get('upper_numerator') == numerator and exact.get('scale') == scale
                    and exact.get('target_numerator') == 51 * scale
                    and evidence.get('triangle_row_validation', {}).get('required') is True,
                    'Saved exact replay does not bind and exclude this active IY case')
            bind(HERE / 'replay_degree17_full.py', REPLAYER_SHA256)
            entry['exact_replay'] = evidence_bound
        rows.append(entry)
        seen.add((kind, case))
    require(seen == {(kind, r['case']) for kind in KINDS for r in orbits}, 'Twelve-case product coverage failed')
    for path, digest in inputs.items():
        require(sha(path) == digest, f'Bound input changed: {path}')
    return dict(status='PASS_INDEPENDENT_IY_COVERAGE_WITH_BOUND_EXACT_REPLAYS' if bind_replays else 'PASS_INDEPENDENT_IY_COVERAGE_ACTIVE_RECEIPTS',
                checker=checker, producer=source, reconstruction='one literal S6 census; no producer imports',
                p9_automorphism_order=6, internal_four_sets=15, internal_orbits=orbits,
                p8_deletion_orbits=deletion_orbits, opposite_forms=list(KINDS), active_case_count=12,
                exact_replays_bound=bind_replays, records=rows,
                all_inputs_unchanged=True, elapsed_seconds=time.monotonic()-started,
                assurance='independent finite marker coverage and input binding; arbitrary-support family bridge and prior I8 classification remain ordinary imports; no model build, solver, new dual replay or Lean')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--bind-replays', action='store_true')
    ap.add_argument('--output', type=Path, default=HERE / 'degree17_full/P9-IY-active-v2-manifest.json')
    args = ap.parse_args()
    require(not args.output.exists(), 'Refusing to overwrite an existing manifest')
    def timeout(_sig, _frame):
        raise TimeoutError('Ten-second finite-coverage deadline expired')
    signal.signal(signal.SIGALRM, timeout)
    signal.setitimer(signal.ITIMER_REAL, 10)
    result = check(args.bind_replays)
    signal.setitimer(signal.ITIMER_REAL, 0)
    with args.output.open('x') as handle:
        json.dump(result, handle, indent=2, allow_nan=False)
        handle.write('\n')
    print(json.dumps(dict(status=result['status'], cases=result['active_case_count'],
                          exact_replays_bound=result['exact_replays_bound'], output=str(args.output.resolve()),
                          elapsed_seconds=result['elapsed_seconds'])))


if __name__ == '__main__':
    main()
