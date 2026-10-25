#!/usr/bin/env python3
"""Independent finite H0 marker coverage and staged receipt/replay manifest.

Standard library only: no producer, numerical package, model build or replay
execution. Default mode requires all 24 completed exact leaf replays.
--active-only still requires all 24 completed strict producer certificates,
but reports no leaf-replay closure. The twelve prior P10 component replays
are required in both modes. Immutable output; thirty-second deadline.
"""
import argparse
import hashlib
import itertools as it
import json
from pathlib import Path
import signal
import time

HERE = Path(__file__).resolve().parent
PRIOR = HERE.parents[1] / 'frontier20261020/prior-art68'
V3 = 'd247fa0ac29e5ea765f5ede2d60df9ff9ce89e905f86f1295161acedceb370ae'
V4 = 'a1beae56f60205a48442a1c6a31d2148557443511fb119a1936ffda8578bebf2'
REPLAY3 = '2e2238bfeb0ba50b98e74d4fe672ed58ee54d017b9a7387da15d875728863824'
REPLAY4 = '024c11d4897818233a74b7fff9f3c925ea521dd52818ec16411bd98ec3650b44'
PHASEONE = '929a101c2ec29570790450d112914f2048a83c78fdf8b5f658f84cb7f4eb8069'
I7_CERT = 'fe172301b201819c029d9a1b7e8931f516cbd90aa978977118b7853b2ead7164'
COMPONENT_SOURCE = '1e3eaa89225246bb695740792bcaf0a5c365eb50c4212467aeb3c9569d7658d0'
COMPONENT_REPLAYER = '1e6ef9e322b31593e12483a1e53937bf950f424d8c29433793f40ed98198608a'
COMPONENT_SUMMARY = 'd130fb5c8f164e4ab6a164e60bd1c2e8f41021da82f48195255a3cc11690711c'


def require(value, message):
    if not value:
        raise ValueError(message)


def integer(value, label):
    require(type(value) is int, label + ' must be an integer')
    return value


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def value_hash(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'),
                                     allow_nan=False).encode()).hexdigest()


def mask(points):
    return sum(1 << v for v in points)


def reconstruct(h0):
    p10 = frozenset(frozenset(map(int, text)) for text in
                   '012 015 023 034 045 124 134 135 235 245'.split())
    ay, az = [], []
    for perm in it.permutations(range(6)):
        for family, group in ((p10, ay), (h0, az)):
            moved = frozenset(frozenset(perm[v] for v in block) for block in family)
            if moved == family:
                group.append(perm)
    require(len(ay) == 60 and len(az) == 6, 'Wrong complete component automorphism groups')
    y, z = frozenset(range(6)), frozenset(range(6, 12))
    group = tuple(a + tuple(v+6 for v in b) + (12,) for a, b in it.product(ay, az))
    domains = {
        'IZ': {frozenset(vs) for vs in it.combinations(z, 4)},
        'E4_': {frozenset(vs) for vs in it.combinations(range(12), 4)
                if set(vs) & y and set(vs) & z},
        'E3_': {frozenset((*vs, 12)) for vs in it.combinations(range(12), 3)
                if set(vs) & y and set(vs) & z},
    }
    records = {}
    for prefix, domain in domains.items():
        unseen, counter = set(domain), 0
        while unseen:
            representative = min(unseen, key=mask)
            orbit = {frozenset(perm[v] for v in representative) for perm in group}
            require(orbit <= unseen, 'Marker orbit overlaps or leaves its literal domain')
            case = f'{prefix}{counter:02d}'
            records[case] = dict(marker=mask(representative), orbit=sorted(map(mask, orbit)),
                                 points=sorted(representative), stage=prefix)
            unseen -= orbit
            counter += 1
        require(counter == {'IZ': 4, 'E4_': 14, 'E3_': 6}[prefix], 'Wrong independent marker orbit count')
        covered = set().union(*(set(r['orbit']) for r in records.values() if r['stage'] == prefix))
        require(covered == set(map(mask, domain)), 'Incomplete literal marker domain')
    require([len(domains[p]) for p in ('IZ', 'E4_', 'E3_')] == [15, 465, 180], 'Wrong finite domains')
    for size in range(3):
        require(all(any(not (set(vs) & block) for block in p10) for vs in it.combinations(y, size)),
                'P10 does not avoid every subset of size at most two')
    require(all(any(v not in block for block in h0) for v in range(6)), 'H0 has a common point')
    transversals = {frozenset(vs) for vs in it.combinations(y, 3)
                    if all(set(vs) & block for block in p10)}
    require(transversals == set(p10), 'P10 triple transversals are not exactly its ten blocks')
    root_link = sorted(map(mask, p10)) + sorted(mask({v+6 for v in block}) for block in h0)
    return records, sorted(root_link), dict(Y=60, Z=6, product=360)


def check(active_only=False):
    started = time.monotonic()
    tracked, parsed = {}, {}

    def bind(path, expected=None):
        path = Path(path).resolve()
        digest = tracked.get(path)
        if digest is None:
            require(path.is_file(), 'Missing required input (pending work): ' + str(path))
            digest = sha(path)
            tracked[path] = digest
        require(expected is None or digest == expected, 'Hash mismatch: ' + str(path))
        return dict(path=str(path), sha256=digest)

    def read(path):
        path = Path(path).resolve()
        bind(path)
        if path not in parsed:
            parsed[path] = json.loads(path.read_text())
        return parsed[path]

    checker = bind(__file__)
    assembly = bind(HERE / 'D17-H0-staged-coverage.md')
    sources = [bind(HERE / 'degree17_full_projection_v3.py', V3),
               bind(HERE / 'degree17_full_projection_v4.py', V4)]
    cert_path = PRIOR / 'repository/companion/terminal/r16/results/seven_certificate.json'
    certificate = bind(cert_path, I7_CERT)
    cert = read(cert_path)
    row = [r for r in cert['rows'] if r['id'] == 0]
    require(len(row) == 1 and row[0].get('support') == 6, 'Missing literal six-point H0')
    h0 = frozenset(frozenset(block) for block in row[0]['blocks'])
    expected_h0 = frozenset(frozenset(map(int, t)) for t in '012 034 134 035 235 145 245'.split())
    require(h0 == expected_h0 and len(h0) == 7 and all(len(t) == 3 for t in h0)
            and all(a & b for a, b in it.combinations(h0, 2))
            and all(not (a & b == a & c == b & c) for a, b, c in it.combinations(h0, 3)),
            'H0 differs from the explicit intersecting SF3 template')
    records, root_link, automorphisms = reconstruct(h0)
    stars = {(1 << 15) | t for t in root_link}

    # These are separately completed exact component replays, not executions
    # by this checker. Their summary pins all twelve original/replay pairs.
    summary_path = HERE / 'degree17-replay/P10-nonempty-summary.json'
    y_summary = bind(summary_path, COMPONENT_SUMMARY)
    summary = read(summary_path)
    require(summary.get('all_pass') is True and summary.get('count') == 12
            and len(summary.get('records', [])) == 12, 'P10 Y-empty dependency is incomplete')
    bind(HERE / 'degree17_component.py', COMPONENT_SOURCE)
    bind(HERE / 'replay_component17.py', COMPONENT_REPLAYER)
    y_inputs, y_replays, orbit_total = {}, [], 0
    for item in summary['records']:
        old_path, replay_path = Path(item['receipt']).resolve(), Path(item['replay']).resolve()
        old_bound = bind(old_path, item['receipt_sha256'])
        replay_bound = bind(replay_path, item['replay_sha256'])
        old, evidence = read(old_path), read(replay_path)
        case = old.get('case', {})
        case_id = case.get('id')
        require(case_id in {f'P10_{i:03d}' for i in range(1, 13)} and case_id not in y_inputs
                and old_path == (HERE / 'degree17' / (case_id + '.json')).resolve()
                and replay_path == (HERE / 'degree17-replay' / (case_id + '-replay.json')).resolve(),
                'Wrong P10 dependency case or path')
        require(case.get('component') == 10 and case.get('outside') == 7
                and case.get('r10') == 0 and case.get('r9') == 0 and bool(case.get('interiors'))
                and old.get('root_degree') == 17 and old.get('point_cap') == 17
                and old.get('mu') == 41 and old.get('min_used_degree') == 7
                and old.get('source_sha256') == COMPONENT_SOURCE, 'Wrong P10 dependency scope')
        require(item.get('result') == 'PASS' and evidence.get('result') == 'PASS'
                and evidence.get('all_bound_inputs_unchanged') is True
                and evidence.get('receipt_sha256') == old_bound['sha256']
                and evidence.get('replayer_sha256') == COMPONENT_REPLAYER
                and evidence.get('case') == case, 'P10 component replay did not pass with matching inputs')
        exact, reported = evidence.get('exact', {}), old.get('certificate', {})
        require(all(integer(exact.get(k), 'component ' + k) == integer(reported.get(k), 'component reported ' + k)
                    for k in ('scale', 'H', 'minimum', 'G'))
                and exact['G'] == exact['H'] - exact['minimum'] and exact['G'] < 0
                and exact.get('negative') is True, 'P10 dependency lacks a strict exact contradiction')
        catalogue = evidence.get('catalogue', {})
        require(catalogue.get('internal_count') == 292 and catalogue.get('automorphism_count') == 60
                and catalogue.get('orbit_count') == 13, 'P10 component coverage differs')
        orbit_total += integer(catalogue.get('orbit_size'), 'component orbit size')
        for relative, digest in old['pinned_dependencies'].items():
            require(not Path(relative).is_absolute() and '..' not in Path(relative).parts, 'Invalid prior path')
            bind(PRIOR / relative, digest)
        for filename, digest in old['ordinary_bridge_sha256'].items():
            bind(HERE / filename, digest)
        y_inputs[case_id] = dict(sha256=old_bound['sha256'], recorded_gap=exact['G'],
                                status='imported recorded exact gap; not independently replayed by this script')
        y_replays.append(dict(case=case_id, original=old_bound, replay=replay_bound, exact_gap=exact['G']))
    require(len(y_inputs) == 12 and orbit_total == 291, 'P10 nonempty dependency coverage is incomplete')
    expected_y_registry = {name + '.json': value for name, value in y_inputs.items()}

    stage_config = {'IZ': ('H0-internal-v3', V3, False, False),
                    'E4_': ('H0-fourcore-v4', V4, True, False),
                    'E3_': ('H0-mixedthree-v4', V4, True, True)}
    active, selected_paths, stage_counts = [], set(), {'IZ': 0, 'E4_': 0, 'E3_': 0}
    for case, marker_record in records.items():
        stage = marker_record['stage']
        label, source, empty_z, no_four = stage_config[stage]
        paths = sorted((HERE / 'degree17_full').glob(f'P10-H0-{case}-{label}-*.json'))
        primary = [p for p in paths if not p.stem.endswith('-phaseone')]
        phases = [p for p in paths if p.stem.endswith('-phaseone')]
        require(len(primary) == 1, 'Missing or ambiguous original leaf (pending work): ' + case)
        original_path = primary[0].resolve()
        original = read(original_path)
        if original.get('status') == 2:
            require(case == 'E4_11' and len(phases) == 1, 'Status2 leaf lacks its one active phase-one certificate')
            active_path = phases[0].resolve()
            data = read(active_path)
            require(data.get('certificate_kind') == 'zero-infeasibility'
                    and data.get('original_status') == 2
                    and data.get('input_receipt_path') == str(original_path)
                    and data.get('input_receipt_sha256') == bind(original_path)['sha256']
                    and data.get('certificate_producer_sha256') == PHASEONE,
                    'Phase-one leaf does not bind the original status2 input')
            bind(HERE / 'degree17_full_phaseone.py', PHASEONE)
            changed = {'status', 'message', 'assurance', 'dual', 'primal_trace'}
            require(all(data.get(k) == v for k, v in original.items() if k not in changed),
                    'Phase one changed mathematical model or premise metadata')
            zero = True
        else:
            require(not phases, 'Unexpected ambiguous phase-one alternative')
            active_path, data, zero = original_path, original, False
        selected_paths.update(p.resolve() for p in paths)
        receipt = bind(active_path)
        require(data.get('status') == 0 and data.get('kind') == 'P10-H0' and data.get('case') == case
                and data.get('source_sha256') == source and data.get('root_degree') == 17
                and data.get('point_cap') == 17 and data.get('mu') == 41
                and data.get('target_residuals') == 51, 'Leaf is unfinished or has the wrong source/scope: ' + case)
        require(data.get('empty_z') is empty_z and data.get('forbid_four_core') is no_four
                and data.get('assigned_z') is None and data.get('forbidden') == []
                and data.get('crowding_imports') is True and type(data.get('degree_distributions')) is bool,
                'Unjustified extra restriction or incorrect stage dependency: ' + case)
        require(data.get('P10_internal_exclusion_receipts') == expected_y_registry,
                'Leaf Y-empty import differs from separately completed P10 exact replays')
        geometry = data.get('geometry', {})
        require(geometry.get('kind') == 'P10-H0' and geometry.get('root') == 15
                and geometry.get('Y') == list(range(6)) and geometry.get('Z') == list(range(6, 12))
                and geometry.get('exterior_marker') == 12 and geometry.get('excluded_Y_internal_count') == 15
                and sorted(geometry.get('link', [])) == root_link
                and geometry.get('automorphism_orders') == automorphisms, 'Wrong complete H0 root geometry')
        require(set(geometry.get('records', {})) == {'none'} | set(records), 'Producer marker catalogue domain differs')
        for name, marker in records.items():
            category = {'IZ': 'internal-Z', 'E4_': 'mixed-four-core', 'E3_': 'mixed-three-core-plus-exterior'}[marker['stage']]
            require(geometry['records'][name] == dict(marker=marker['marker'], category=category,
                                                     orbit_size=len(marker['orbit']), orbit=marker['orbit']),
                    'Producer orbit differs from independent marker reconstruction')
        imports = data.get('imported_crowding_sources', {})
        require(bool(imports), 'Missing imported theorem/source registry')
        for item in imports.values():
            bind(item['path'], item['sha256'])
        bind(HERE / 'D18-structural-tools.md', data['structural_note_sha256'])
        bind(HERE / 'D18-pool-research.md', data['pool_note_sha256'])
        bind(PRIOR / 'repository/companion/upstream/MU42/scripts/local43.py', data['imported_local43_sha256'])
        clique = data.get('h27_cliques')
        require(isinstance(clique, dict), 'Expected literal H0 clique dependency')
        bind(clique['path'], clique['sha256'])
        for item in clique['sources'].values():
            bind(item['path'], item['sha256'])
        require(clique.get('source_kind') == 'P10-H0' and clique.get('excluded_points') == [15]
                and set(clique.get('fixed_members', [])) <= stars | {marker_record['marker']},
                'Clique dependency assumes an unselected actual member')
        identity = dict(source_sha256=source, imported_local43_sha256=data['imported_local43_sha256'],
                        structural_note_sha256=data['structural_note_sha256'], pool_note_sha256=data['pool_note_sha256'],
                        imported_crowding_sources=imports, P10_internal_exclusion_receipts=expected_y_registry,
                        kind='P10-H0', literal_premises=data['literal_premises'], h27_cliques=clique)
        require(value_hash(identity) == data.get('premise_sha256'), 'Leaf premise fingerprint differs')
        dual = data.get('dual', {})
        for field in ('scale', 'H', 'correction', 'upper_numerator'):
            integer(dual.get(field), case + ' ' + field)
        threshold = 0 if zero else 51 * dual['scale']
        require(dual['scale'] > 0 and dual['upper_numerator'] == dual['H'] + dual['correction']
                and dual['upper_numerator'] < threshold
                and dual.get('below0' if zero else 'below51') is True
                and dual.get('objective', 'trace') == ('zero' if zero else 'trace'),
                'Leaf has no completed strict reported certificate: ' + case)
        entry = dict(case=case, stage=stage, marker=marker_record['marker'], orbit=marker_record['orbit'],
                     active_receipt=receipt, source_sha256=source, premise_sha256=data['premise_sha256'],
                     certificate_kind='zero-infeasibility' if zero else 'trace-upper-bound',
                     reported_upper_numerator=dual['upper_numerator'], scale=dual['scale'],
                     target_numerator=threshold, h27_clique_dependency=clique)
        if zero:
            entry['superseded_status2_input'] = bind(original_path)
        if not active_only:
            replay_path = HERE / 'degree17_full_replay' / (active_path.stem + '-replay.json')
            evidence_bound = bind(replay_path)
            evidence = read(replay_path)
            exact = evidence.get('exact_replay', {})
            replayer = evidence.get('replayer_sha256')
            require(replayer in ({REPLAY3, REPLAY4} if source == V3 else {REPLAY4}), 'Wrong leaf exact replayer version')
            bind(HERE / ('replay_degree17_full_v3.py' if replayer == REPLAY3 else 'replay_degree17_full_v4.py'), replayer)
            require(evidence.get('result') == 'PASS' and evidence.get('all_inputs_unchanged') is True
                    and evidence.get('receipt_sha256') == receipt['sha256']
                    and evidence.get('source', {}).get('sha256') == source
                    and evidence.get('premise_sha256') == data['premise_sha256']
                    and evidence.get('certificate_kind') == entry['certificate_kind']
                    and exact.get('strict_exclusion') is True
                    and all(exact.get(k) == dual[k] for k in ('scale', 'H', 'correction', 'upper_numerator'))
                    and exact.get('target_numerator') == threshold
                    and evidence.get('P10_exclusion_binding', {}).get('required') is True
                    and evidence.get('triangle_row_validation', {}).get('required') is True
                    and evidence.get('h27_clique_row_validation', {}).get('required') is True,
                    'Leaf exact replay is missing, unfinished or inconsistent: ' + case)
            if source == V4:
                require(evidence.get('marked_B4_validation', {}).get('required') is True
                        and evidence['marked_B4_validation'].get('pruning_checked') is True,
                        'v4 replay lacks B4 row/pruning verification')
            if zero:
                require(exact.get('all_objective_coefficients_zero') is True and exact.get('G') == dual['upper_numerator'],
                        'Phase-one replay did not use the zero objective')
            entry['exact_replay'] = evidence_bound
        active.append(entry)
        stage_counts[stage] += 1
    all_stage_paths = {p.resolve() for label, *_ in stage_config.values()
                       for p in (HERE / 'degree17_full').glob(f'P10-H0-*-{label}-*.json')}
    require(all_stage_paths == selected_paths and stage_counts == {'IZ': 4, 'E4_': 14, 'E3_': 6},
            'Stage files are incomplete, ambiguous or outside the reconstructed product domains')
    for path, digest in tracked.items():
        require(sha(path) == digest, 'Bound input changed during inspection: ' + str(path))
    return dict(status='PASS_H0_INDEPENDENT_STAGED_COVERAGE_ACTIVE_ONLY' if active_only else 'PASS_H0_INDEPENDENT_STAGED_COVERAGE_EXACT_BOUND',
                checker=checker, ordinary_assembly=assembly, producers=sources, I7_certificate=certificate,
                literal_H0=sorted(map(mask, h0)), automorphism_orders=automorphisms,
                finite_domains=dict(IZ=15, E4=465, E3=180), stage_orbit_counts=stage_counts,
                marker_orbits=records, active_leaf_count=24, exact_leaf_replays_bound=not active_only,
                Y_empty_dependency=dict(summary=y_summary, exact_replays=y_replays, nonempty_assignments=291),
                stages=[dict(name='IZ', assumes=['Y-empty'], proves='Z-empty'),
                        dict(name='E4_', assumes=['Y-empty', 'Z-empty'], proves='all four-core residuals absent'),
                        dict(name='E3_', assumes=['Y-empty', 'Z-empty', 'all four-core residuals absent'],
                             proves='all mixed-three-core residuals absent')],
                terminal_literal_checks=dict(Y_avoids_every_at_most_two=True, Z_avoids_every_at_most_one=True,
                                             Y_triple_transversals_exactly_P10=True, conditional_residual_bound=37, required_residuals=51),
                records=active, all_inputs_unchanged=True, elapsed_seconds=time.monotonic()-started,
                assurance='independent finite marker coverage and staged input/existing-replay binding; no model build, solver or new exact replay; ordinary family bridge, terminal proof and prior theorems remain explicit imports')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--active-only', action='store_true')
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    suffix = 'active' if args.active_only else 'replayed'
    output = args.output or HERE / f'degree17_full/P10-H0-staged-{suffix}-manifest.json'
    require(not output.exists(), 'Refusing to overwrite an existing manifest')
    def timeout(_sig, _frame):
        raise TimeoutError('Thirty-second finite coverage/binding deadline expired')
    signal.signal(signal.SIGALRM, timeout)
    signal.setitimer(signal.ITIMER_REAL, 30)
    result = check(args.active_only)
    signal.setitimer(signal.ITIMER_REAL, 0)
    with output.open('x') as handle:
        json.dump(result, handle, indent=2, allow_nan=False)
        handle.write('\n')
    print(json.dumps(dict(status=result['status'], stages=result['stage_orbit_counts'],
                          exact_leaf_replays_bound=result['exact_leaf_replays_bound'], output=str(output.resolve()),
                          elapsed_seconds=result['elapsed_seconds'])))


if __name__ == '__main__':
    main()
