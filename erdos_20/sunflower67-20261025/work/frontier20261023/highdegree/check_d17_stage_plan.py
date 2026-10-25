#!/usr/bin/env python3
"""Independent literal D17 marker-stage coverage from an explicit proof plan.

No producer import, model build, numerical package, solver or new exact replay.
Every listed node names an already completed receipt and replay plus earlier
antecedent node IDs. Unknown producers and extra-member splits fail closed.
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
SOURCES = {
    '3d79ea4a0755f59aa8107c89d773600bc0965aa751772c337c3431c3a7caff52': ('degree17_full_projection.py', 1),
    '497f71f4fdf555c7456b42123684e7fd5059769f89662c257e2263425798b31a': ('degree17_full_projection_v2.py', 2),
    'd247fa0ac29e5ea765f5ede2d60df9ff9ce89e905f86f1295161acedceb370ae': ('degree17_full_projection_v3.py', 3),
    'a1beae56f60205a48442a1c6a31d2148557443511fb119a1936ffda8578bebf2': ('degree17_full_projection_v4.py', 4),
}
REPLAYERS = {
    '3ac2265ad2fd090bf2b06e012ed8c9551f6e7e3bb9d0d7f903fb7d3a756a937b': ('replay_degree17_full.py', 2),
    '2e2238bfeb0ba50b98e74d4fe672ed58ee54d017b9a7387da15d875728863824': ('replay_degree17_full_v3.py', 3),
    '024c11d4897818233a74b7fff9f3c925ea521dd52818ec16411bd98ec3650b44': ('replay_degree17_full_v4.py', 4),
}
I7_CERT = 'fe172301b201819c029d9a1b7e8931f516cbd90aa978977118b7853b2ead7164'
PHASEONE = '929a101c2ec29570790450d112914f2048a83c78fdf8b5f658f84cb7f4eb8069'
COMPONENT_SOURCE = '1e3eaa89225246bb695740792bcaf0a5c365eb50c4212467aeb3c9569d7658d0'
COMPONENT_REPLAY = '1e6ef9e322b31593e12483a1e53937bf950f424d8c29433793f40ed98198608a'
COMPONENT_SUMMARY = 'd130fb5c8f164e4ab6a164e60bd1c2e8f41021da82f48195255a3cc11690711c'
I7_TEXT = (
    '012 034 134 035 235 145 245', '012 034 234 135 235 145 245',
    '012 134 234 135 235 145 245', '013 024 134 125 235 045 345',
    '023 124 134 125 235 045 345', '014 234 025 125 035 145 345',
    '134 234 125 035 135 045 245', '023 024 034 124 134 015 016',
)
KINDS = tuple(f'P10-H{i}' for i in range(8)) + ('P9-P8-i1', 'P9-P8-i2', 'P9-Q8')


def require(value, message):
    if not value:
        raise ValueError(message)


def integer(value, name):
    require(type(value) is int, name + ' must be an integer')
    return value


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def value_hash(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'),
                                     allow_nan=False).encode()).hexdigest()


def mask(points):
    return sum(1 << v for v in points)


def family(text):
    return frozenset(frozenset(map(int, block)) for block in text.split())


def autos(fam, n):
    return tuple(p for p in it.permutations(range(n))
                 if frozenset(frozenset(p[v] for v in block) for block in fam) == fam)


def reconstruct(kind, certificate):
    """Enumerate only literal component permutations and marker orbits."""
    p10 = family('012 015 023 034 045 124 134 135 235 245')
    ap10 = autos(p10, 6)
    require(len(ap10) == 60, 'Wrong complete P10 automorphism group')
    require([r['id'] for r in certificate['rows']] == list(range(8)), 'Incomplete I7 certificate')
    for i, row in enumerate(certificate['rows']):
        actual = frozenset(map(frozenset, row['blocks']))
        require(actual == family(I7_TEXT[i]) and row['support'] == (7 if i == 7 else 6)
                and all(a & b for a, b in it.combinations(actual, 2))
                and all(not (a & b == a & c == b & c) for a, b, c in it.combinations(actual, 3)),
                'I7 row differs from its literal intersecting SF3 template')
    empty_y = kind.startswith('P10-')
    ylink = p10 if empty_y else p10 - {frozenset((0, 1, 2))}
    omitted, deletion_orbit = [], []
    if empty_y:
        number = int(kind[5:])
        zlocal = family(I7_TEXT[number])
        zsize = 7 if number == 7 else 6
    elif kind == 'P9-Q8':
        zlocal = frozenset(frozenset((h, *ab)) for h in (0, 1)
                          for ab in it.combinations((2, 3, 4), 2)) | family('015 016')
        zsize = 7
    else:
        pairs = {tuple(sorted(map(mask, ab))) for ab in it.combinations(p10, 2)}
        unseen, types = set(pairs), {}
        while unseen:
            rep = min(unseen)
            orbit = {tuple(sorted(mask(p[v] for v in range(6) if t >> v & 1) for t in rep)) for p in ap10}
            require(orbit <= unseen, 'P8 deletion orbits overlap')
            intersection = (rep[0] & rep[1]).bit_count()
            require(intersection in (1, 2) and intersection not in types, 'Unexpected deletion type')
            types[intersection] = (rep, sorted(orbit))
            unseen -= orbit
        require(set(types) == {1, 2}, 'Incomplete P8 deletion types')
        omitted, deletion_orbit = types[int(kind[-1])]
        zlocal = frozenset(t for t in p10 if mask(t) not in omitted)
        zsize = 6
    core = 6 + zsize
    y, z = frozenset(range(6)), frozenset(range(6, core))
    ay, az = autos(ylink, 6), autos(zlocal, zsize)
    group = tuple(a + tuple(v+6 for v in b) + (core,) for a, b in it.product(ay, az))
    domains = {
        'IY': set() if empty_y else {frozenset(vs) for vs in it.combinations(y, 4)},
        'IZ': {frozenset(vs) for vs in it.combinations(z, 4)},
        'E4_': {frozenset(vs) for vs in it.combinations(range(core), 4) if set(vs) & y and set(vs) & z},
        'E3_': {frozenset((*vs, core)) for vs in it.combinations(range(core), 3) if set(vs) & y and set(vs) & z},
    }
    categories = {'IY': 'internal-Y', 'IZ': 'internal-Z', 'E4_': 'mixed-four-core',
                  'E3_': 'mixed-three-core-plus-exterior'}
    records = {'none': dict(marker=None, category='unmarked', orbit_size=0, orbit=[])}
    counts = {}
    for prefix, domain in domains.items():
        unseen, counter = set(domain), 0
        while unseen:
            representative = min(unseen, key=mask)
            orbit = {frozenset(p[v] for v in representative) for p in group}
            require(orbit <= unseen, 'A marker orbit overlaps or leaves its literal domain')
            records[f'{prefix}{counter:02d}'] = dict(marker=mask(representative),
                category=categories[prefix], orbit_size=len(orbit), orbit=sorted(map(mask, orbit)))
            unseen -= orbit
            counter += 1
        counts[prefix] = counter
    for size in range(3):
        require(all(any(not (set(vs) & block) for block in ylink) for vs in it.combinations(y, size)),
                'Y does not avoid every subset of size at most two')
    require(all(any(v not in block for block in zlocal) for v in range(zsize)), 'Z has a common point')
    ty = {frozenset(vs) for vs in it.combinations(y, 3) if all(set(vs) & block for block in ylink)}
    ty_capacity = sum(2-int(t in ylink) for t in ty)
    require(ty_capacity == (10 if empty_y else 13), 'Wrong transversal completion capacity')
    root_link = sorted(map(mask, ylink)) + sorted(mask(v+6 for v in t) for t in zlocal)
    return dict(core=core, empty_y=empty_y, Y=mask(y), Z=mask(z), records=records,
                root_link=sorted(root_link), stars={(1 << 15) | t for t in root_link},
                automorphisms=dict(Y=len(ay), Z=len(az), product=len(group)),
                omitted=list(omitted), deletion_orbit=[list(pair) for pair in deletion_orbit],
                orbit_counts=counts, domain_counts={k: len(v) for k, v in domains.items()},
                all_four={mask(vs) for vs in it.combinations(range(core), 4)},
                z_four={mask(vs) for vs in it.combinations(z, 4)},
                y_four={mask(vs) for vs in it.combinations(y, 4)},
                mixed_three={mask(s - {core}) for s in domains['E3_']},
                transversal_masks=sorted(map(mask, ty)), transversal_capacity=ty_capacity)


def bind_p10(path, bind, read):
    summary_bound = bind(path, COMPONENT_SUMMARY)
    summary = read(path)
    require(summary.get('all_pass') is True and summary.get('count') == 12
            and len(summary.get('records', [])) == 12, 'Incomplete P10 component exclusion package')
    bind(HERE / 'degree17_component.py', COMPONENT_SOURCE)
    bind(HERE / 'replay_component17.py', COMPONENT_REPLAY)
    registry, records, total = {}, [], 0
    for item in summary['records']:
        original = bind(item['receipt'], item['receipt_sha256'])
        replay = bind(item['replay'], item['replay_sha256'])
        old, evidence = read(item['receipt']), read(item['replay'])
        case = old.get('case', {})
        cid = case.get('id')
        require(cid in {f'P10_{i:03d}' for i in range(1, 13)} and cid + '.json' not in registry
                and case.get('component') == 10 and case.get('outside') == 7
                and case.get('r10') == case.get('r9') == 0 and bool(case.get('interiors'))
                and old.get('root_degree') == old.get('point_cap') == 17 and old.get('mu') == 41
                and old.get('min_used_degree') == 7 and old.get('source_sha256') == COMPONENT_SOURCE,
                'Wrong P10 component scope or duplicate case')
        require(item.get('result') == evidence.get('result') == 'PASS'
                and evidence.get('all_bound_inputs_unchanged') is True
                and evidence.get('receipt_sha256') == original['sha256']
                and evidence.get('replayer_sha256') == COMPONENT_REPLAY and evidence.get('case') == case,
                'Unbound or unfinished P10 component replay')
        exact, reported = evidence.get('exact', {}), old.get('certificate', {})
        require(all(integer(exact.get(k), k) == integer(reported.get(k), k) for k in ('scale', 'H', 'minimum', 'G'))
                and exact['G'] == exact['H'] - exact['minimum'] and exact['G'] < 0
                and exact.get('negative') is True, 'P10 component gap is not exactly negative')
        catalogue = evidence.get('catalogue', {})
        require(catalogue.get('internal_count') == 292 and catalogue.get('automorphism_count') == 60
                and catalogue.get('orbit_count') == 13, 'Wrong component coverage')
        total += integer(catalogue.get('orbit_size'), 'component orbit size')
        for relative, digest in old['pinned_dependencies'].items():
            require(not Path(relative).is_absolute() and '..' not in Path(relative).parts, 'Invalid prior path')
            bind(PRIOR / relative, digest)
        for filename, digest in old['ordinary_bridge_sha256'].items():
            bind(HERE / filename, digest)
        registry[cid + '.json'] = dict(sha256=original['sha256'], recorded_gap=exact['G'],
            status='imported recorded exact gap; not independently replayed by this script')
        records.append(dict(case=cid, receipt=original, replay=replay, exact_gap=exact['G']))
    require(len(registry) == 12 and total == 291, 'P10 nonempty coverage incomplete')
    return registry, dict(summary=summary_bound, records=records, nonempty_assignments=291)


def check(plan_path, allow_partial=False):
    started = time.monotonic()
    plan_path = Path(plan_path).resolve()
    tracked, parsed = {}, {}

    def resolve(path):
        path = Path(path)
        return (path if path.is_absolute() else plan_path.parent / path).resolve()

    def bind(path, expected=None):
        path = resolve(path)
        require(path.is_file(), 'Missing required input (pending work): ' + str(path))
        digest = tracked.get(path)
        if digest is None:
            digest = sha(path)
            tracked[path] = digest
        require(expected is None or digest == expected, 'Input hash mismatch: ' + str(path))
        return dict(path=str(path), sha256=digest)

    def read(path):
        path = resolve(path)
        bind(path)
        if path not in parsed:
            parsed[path] = json.loads(path.read_text())
        return parsed[path]

    checker, plan_bound = bind(__file__), bind(plan_path)
    ordinary = bind(HERE / 'D17-generic-stage-plan.md')
    plan = read(plan_path)
    require(isinstance(plan, dict) and plan.get('schema') == 'd17-stage-proof-plan-v1'
            and set(plan) <= {'schema', 'kind', 'p10_internal_summary', 'nodes', 'construction_inputs', 'unproved_candidates'}
            and plan.get('kind') in KINDS and isinstance(plan.get('nodes'), list), 'Invalid explicit plan schema')
    kind = plan['kind']
    construction_inputs = plan.get('construction_inputs', [])
    require(isinstance(construction_inputs, list), 'Construction inputs must be an explicit list')
    for item in construction_inputs:
        require(isinstance(item, dict) and set(item) == {'path', 'sha256'}, 'Malformed construction input')
        bind(item['path'], item['sha256'])
    cert_path = PRIOR / 'repository/companion/terminal/r16/results/seven_certificate.json'
    certificate = bind(cert_path, I7_CERT)
    g = reconstruct(kind, read(cert_path))
    unproved = plan.get('unproved_candidates', [])
    require(isinstance(unproved, list), 'Unproved candidates must be an explicit diagnostic list')
    for item in unproved:
        require(isinstance(item, dict) and set(item) == {'case', 'receipt', 'receipt_sha256'}
                and item['case'] in g['records'], 'Malformed unproved candidate')
        bind(item['receipt'], item['receipt_sha256'])
    if g['empty_y']:
        require('p10_internal_summary' in plan, 'P10 requires an explicit prior component summary path')
        y_registry, y_dependency = bind_p10(plan['p10_internal_summary'], bind, read)
    else:
        require('p10_internal_summary' not in plan, 'P9 must not import P10 Y-emptiness')
        y_registry, y_dependency = {}, None
    base_four = set(g['y_four']) if g['empty_y'] else set()
    facts, records, direct = {}, [], False
    for node in plan['nodes']:
        require(isinstance(node, dict) and set(node) <= {'id', 'receipt', 'replay', 'receipt_sha256', 'replay_sha256', 'uses'}
                and {'id', 'receipt', 'replay', 'uses'} <= set(node), 'Invalid proof node schema')
        nid, uses = node['id'], node['uses']
        require(isinstance(nid, str) and bool(nid) and nid not in facts
                and isinstance(uses, list) and all(isinstance(u, str) and u in facts for u in uses)
                and len(set(uses)) == len(uses), 'Node IDs/antecedents must be distinct and strictly earlier')
        prior_four, prior_three = set(base_four), set()
        for previous in uses:
            prior_four |= facts[previous][0]
            prior_three |= facts[previous][1]
        receipt = bind(node['receipt'], node.get('receipt_sha256'))
        replay_bound = bind(node['replay'], node.get('replay_sha256'))
        data, evidence = read(node['receipt']), read(node['replay'])
        source = data.get('source_sha256')
        require(source in SOURCES, 'Unknown producer; an explicit inspected adapter is required')
        source_file, version = SOURCES[source]
        bind(HERE / source_file, source)
        case = data.get('case')
        require(case in g['records'] and data.get('kind') == kind and data.get('status') == 0
                and data.get('root_degree') == data.get('point_cap') == 17 and data.get('mu') == 41
                and data.get('target_residuals') == 51 and data.get('crowding_imports') is True
                and type(data.get('degree_distributions')) is bool
                and type(data.get('empty_z')) is bool and type(data.get('forbid_four_core')) is bool,
                'Unfinished leaf or incorrect D17 scope')
        require(not any(k in data for k in ('extra_members', 'selected_actual_members', 'represented_points')),
                'Extra-actual-member splits require their own coverage adapter')
        selected = g['records'][case]['marker']
        n = g['core'] + int(selected is not None and bool(selected >> g['core']))
        core_mask, represented_mask = (1 << g['core'])-1, (1 << n)-1
        forbidden = data.get('forbidden')
        require(isinstance(forbidden, list) and all(type(s) is int and 0 <= s <= represented_mask and s.bit_count() <= 4 for s in forbidden),
                'Malformed forbidden exact traces')
        for s in forbidden:
            c = s & core_mask
            require((c.bit_count() == 4 and c in prior_four)
                    or (c.bit_count() == 3 and c in prior_three),
                    f'Node {nid} assumes an unproved forbidden trace {s}')
        require(not data['empty_z'] or g['z_four'] <= prior_four, 'empty_z lacks complete earlier Z exclusions')
        require(not data['forbid_four_core'] or g['all_four'] <= prior_four, 'forbid_four_core lacks complete earlier four-core exclusions')
        assigned = data.get('assigned_z')
        require(assigned is None or assigned == [] and g['z_four'] <= prior_four,
                'Only independently justified empty assigned-Z patterns are supported')
        require(data.get('P10_internal_exclusion_receipts', {}) == y_registry, 'Wrong P10 Y-empty registry')
        geometry = data.get('geometry', {})
        require(geometry.get('kind') == kind and geometry.get('root') == 15
                and geometry.get('Y') == list(range(6)) and geometry.get('Z') == list(range(6, g['core']))
                and geometry.get('exterior_marker') == g['core']
                and geometry.get('excluded_Y_internal_count') == (15 if g['empty_y'] else 0)
                and sorted(geometry.get('link', [])) == g['root_link']
                and geometry.get('automorphism_orders') == g['automorphisms']
                and geometry.get('records') == g['records']
                and geometry.get('omitted_local_p10_blocks') == g['omitted']
                and geometry.get('p8_deletion_orbit') == g['deletion_orbit'],
                'Producer geometry differs from independently reconstructed literal geometry')
        imports = data.get('imported_crowding_sources', {})
        require(bool(imports), 'Missing ordinary source registry')
        for item in imports.values():
            bind(item['path'], item['sha256'])
        bind(HERE / 'D18-structural-tools.md', data['structural_note_sha256'])
        bind(HERE / 'D18-pool-research.md', data['pool_note_sha256'])
        bind(PRIOR / 'repository/companion/upstream/MU42/scripts/local43.py', data['imported_local43_sha256'])
        clique = data.get('h27_cliques')
        if clique is not None:
            require(version >= 3 and isinstance(clique, dict), 'Unsupported H27 dependency')
            bind(clique['path'], clique['sha256'])
            for item in clique['sources'].values():
                bind(item['path'], item['sha256'])
            require(clique.get('source_kind') == kind and clique.get('excluded_points') == [15]
                    and set(clique.get('fixed_members', [])) <= g['stars'] | ({selected} if selected is not None else set()),
                    'H27 data assumes an unselected actual member')
        branch = dict(case=case, actual_marker=selected, empty_z=data['empty_z'], assigned_z=assigned,
                      forbidden=forbidden, forbid_four_core=data['forbid_four_core'],
                      degree_distributions=data['degree_distributions'], crowding_imports=True)
        if version >= 3:
            branch['h27_cliques'] = clique
        require(data['literal_premises'][-1] == branch, 'Unexpected literal branch premise')
        identity = dict(source_sha256=source, imported_local43_sha256=data['imported_local43_sha256'],
                        structural_note_sha256=data['structural_note_sha256'], pool_note_sha256=data['pool_note_sha256'],
                        imported_crowding_sources=imports, P10_internal_exclusion_receipts=y_registry,
                        kind=kind, literal_premises=data['literal_premises'])
        if version >= 3:
            identity['h27_cliques'] = clique
        require(value_hash(identity) == data.get('premise_sha256'), 'Premise fingerprint mismatch')
        zero = data.get('certificate_kind') == 'zero-infeasibility'
        if zero:
            bind(HERE / 'degree17_full_phaseone.py', PHASEONE)
            original_bound = bind(data['input_receipt_path'], data['input_receipt_sha256'])
            original = read(data['input_receipt_path'])
            require(data.get('original_status') == 2 and original.get('status') == 2
                    and data.get('certificate_producer_sha256') == PHASEONE,
                    'Phase-one receipt lacks its exact original status2 input')
            changed = {'status', 'message', 'assurance', 'dual', 'primal_trace'}
            require(all(data.get(k) == v for k, v in original.items() if k not in changed),
                    'Phase one changed mathematical model or premises')
        else:
            require(data.get('certificate_kind') in (None, 'trace-upper-bound'), 'Unsupported certificate kind')
        dual = data.get('dual', {})
        for key in ('scale', 'H', 'correction', 'upper_numerator'):
            integer(dual.get(key), key)
        target = 0 if zero else 51 * dual['scale']
        require(dual['scale'] > 0 and dual['upper_numerator'] == dual['H'] + dual['correction']
                and dual['upper_numerator'] < target and dual.get('below0' if zero else 'below51') is True
                and dual.get('objective', 'trace') == ('zero' if zero else 'trace'), 'Leaf lacks a strict certificate')
        replayer = evidence.get('replayer_sha256')
        require(replayer in REPLAYERS and REPLAYERS[replayer][1] >= version, 'Wrong exact replayer adapter')
        bind(HERE / REPLAYERS[replayer][0], replayer)
        exact = evidence.get('exact_replay', {})
        certificate_kind = 'zero-infeasibility' if zero else 'trace-upper-bound'
        require(evidence.get('result') == 'PASS' and evidence.get('all_inputs_unchanged') is True
                and evidence.get('receipt_sha256') == receipt['sha256']
                and evidence.get('source', {}).get('sha256') == source
                and evidence.get('premise_sha256') == data['premise_sha256']
                and evidence.get('certificate_kind') == certificate_kind and exact.get('strict_exclusion') is True
                and all(exact.get(k) == dual[k] for k in ('scale', 'H', 'correction', 'upper_numerator'))
                and exact.get('target_numerator') == target
                and evidence.get('P10_exclusion_binding', {}).get('required') is g['empty_y'],
                'Leaf exact replay is missing, unfinished, nonstrict or inconsistent')
        if version >= 2:
            require(evidence.get('triangle_row_validation', {}).get('required') is True, 'Missing independent triangle-row validation')
        if clique is not None:
            require(evidence.get('h27_clique_row_validation', {}).get('required') is True, 'Missing independent H27-row validation')
        if version >= 4:
            require(evidence.get('marked_B4_validation', {}).get('required') is True
                    and evidence['marked_B4_validation'].get('pruning_checked') is True, 'Missing B4 row/pruning validation')
        if zero:
            require(exact.get('all_objective_coefficients_zero') is True and exact.get('G') == dual['upper_numerator'],
                    'Phase-one replay did not use the zero objective')
        new_four, new_three = set(), set()
        if selected is None:
            direct = True
        elif case.startswith('E3_'):
            new_three = {s & core_mask for s in g['records'][case]['orbit']}
        else:
            new_four = set(g['records'][case]['orbit'])
        facts[nid] = (prior_four | new_four, prior_three | new_three)
        record = dict(id=nid, uses=uses, case=case, receipt=receipt, replay=replay_bound,
                      source_sha256=source, premise_sha256=data['premise_sha256'],
                      certificate_kind=certificate_kind, upper_numerator=dual['upper_numerator'],
                      scale=dual['scale'], target_numerator=target,
                      new_absent_core_four=sorted(new_four), new_absent_mixed_core_three=sorted(new_three),
                      prior_four_count=len(prior_four), prior_mixed_three_count=len(prior_three))
        if zero:
            record['superseded_status2_input'] = original_bound
        records.append(record)
    all_four, all_three = set(base_four), set()
    for four, three in facts.values():
        all_four |= four
        all_three |= three
    missing_four, missing_three = g['all_four']-all_four, g['mixed_three']-all_three
    complete = direct or not missing_four and not missing_three
    require(allow_partial or complete, 'Incomplete stage coverage; use --allow-partial only for an explicitly partial facts report')
    for path, digest in tracked.items():
        require(sha(path) == digest, 'Bound input changed during inspection: ' + str(path))
    return dict(status='PASS_D17_EXPLICIT_STAGE_COVERAGE_EXACT_BOUND' if complete else 'PASS_D17_PARTIAL_STAGE_FACTS_ONLY',
                checker=checker, ordinary_note=ordinary, plan=plan_bound, kind=kind,
                classification_certificate=certificate, automorphism_orders=g['automorphisms'],
                domain_counts=g['domain_counts'], marker_orbit_counts=g['orbit_counts'],
                exact_leaf_count=len(records), records=records, Y_empty_dependency=y_dependency,
                unproved_candidates=unproved,
                absent_core_four=sorted(all_four), absent_mixed_core_three=sorted(all_three),
                missing_core_four=sorted(missing_four), missing_mixed_core_three=sorted(missing_three),
                direct_unmarked_exclusion=direct, complete_kind_coverage=bool(complete),
                terminal=dict(applicable=not missing_four and not missing_three,
                              Y_avoids_every_at_most_two=True, Z_avoids_every_at_most_one=True,
                              Y_triple_transversals=g['transversal_masks'], TY_capacity=g['transversal_capacity'],
                              conditional_residual_bound=27+g['transversal_capacity'], required_residuals=51),
                all_inputs_unchanged=True, elapsed_seconds=time.monotonic()-started,
                assurance='Independent literal marker geometry, explicit antecedent coverage and binding of existing exact replays. No producer import, model build, solver or new replay. Universal classification, row theorems and terminal H27 remain stated ordinary imports; no whole-D17 claim.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('plan', type=Path)
    parser.add_argument('--allow-partial', action='store_true')
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    require(not args.output.exists(), 'Refusing to overwrite an existing coverage output')
    def timeout(_signum, _frame):
        raise TimeoutError('Thirty-second literal stage-plan deadline expired')
    signal.signal(signal.SIGALRM, timeout)
    signal.setitimer(signal.ITIMER_REAL, 30)
    result = check(args.plan, args.allow_partial)
    signal.setitimer(signal.ITIMER_REAL, 0)
    with args.output.open('x') as handle:
        json.dump(result, handle, indent=2, allow_nan=False)
        handle.write('\n')
    print(json.dumps(dict(status=result['status'], kind=result['kind'], leaves=result['exact_leaf_count'],
                          complete=result['complete_kind_coverage'], output=str(args.output.resolve()),
                          elapsed_seconds=result['elapsed_seconds'])))


if __name__ == '__main__':
    main()
