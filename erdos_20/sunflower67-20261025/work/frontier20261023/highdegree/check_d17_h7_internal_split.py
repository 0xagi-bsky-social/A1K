#!/usr/bin/env python3
"""Bind H7's17 earlier internal exclusions and its equality/two-leaf split.

No producer import, model build, solver or new exact LP replay. Reuses the
hash-pinned independent literal stage/equality checkers and existing replays.
The result proves only internal-Z emptiness, conditional on ordinary imports.
"""
import argparse
import hashlib
import importlib.util
import itertools as it
import json
from pathlib import Path
import signal
import time

HERE = Path(__file__).resolve().parent
GENERIC = '0bb364e1ab320773835889c634e28371f7afc85d77e4442e5cdcba5bc8956375'
EQUALITY = '4d94420d153502baf457648614f6006f353aa21560d2e6fb878077f481c74d3e'
V5 = 'bee8278d87557a3f979d7c69022d62d775e74f093cb87ece2c935e6f1acd1210'
REPLAY5 = '36dcd374eb4bcc978eb72ee600410ef725ad1738bebc0d585bf2790a1aea1a10'
PHASE5 = '957d9fd1e1fa162a3f3a18a1937a5cc613078552c4ca607dc76c60d67cb568f8'


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def value_hash(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'),
                                     allow_nan=False).encode()).hexdigest()


def check(plan_path):
    start = time.monotonic()
    plan_path = Path(plan_path).resolve()
    tracked = {}

    def bind(path, expected=None):
        path = Path(path)
        path = (path if path.is_absolute() else plan_path.parent / path).resolve()
        require(path.is_file(), 'Missing required completed input: ' + str(path))
        digest = tracked.get(path)
        if digest is None:
            digest = sha(path)
            tracked[path] = digest
        require(expected is None or digest == expected, 'Changed input: ' + str(path))
        return dict(path=str(path), sha256=digest)

    def read(bound):
        return json.loads(Path(bound['path']).read_text())

    def load_checker(filename, expected):
        bound = bind(HERE / filename, expected)
        spec = importlib.util.spec_from_file_location(filename[:-3], bound['path'])
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        return module, bound

    checker, plan_bound = bind(__file__), bind(plan_path)
    ordinary = bind(HERE / 'D17-H7-internal-split-coverage.md')
    plan = read(plan_bound)
    require(set(plan) == {'schema', 'earlier_plan', 'equality_receipt', 'branches'}
            and plan['schema'] == 'd17-h7-internal-split-plan-v1', 'Invalid explicit H7 split plan')
    generic, generic_bound = load_checker('check_d17_stage_plan.py', GENERIC)
    earlier_plan = bind(plan['earlier_plan']['path'], plan['earlier_plan']['sha256'])
    earlier = generic.check(earlier_plan['path'], allow_partial=True)
    require(earlier['kind'] == 'P10-H7' and earlier['all_inputs_unchanged'] is True
            and earlier['exact_leaf_count'] == 17
            and {r['case'] for r in earlier['records']} == {f'IZ{i:02d}' for i in range(18) if i != 13}
            and not earlier['direct_unmarked_exclusion'] and not earlier['absent_mixed_core_three'],
            'Earlier plan must prove exactly the17 other internal marker cases')
    equality, equality_bound = load_checker('check_d17_h7_equality.py', EQUALITY)
    eq_bound = bind(plan['equality_receipt']['path'], plan['equality_receipt']['sha256'])
    saved, fresh = read(eq_bound), equality.check()
    require({k: v for k, v in saved.items() if k != 'elapsed_seconds'} ==
            {k: v for k, v in fresh.items() if k != 'elapsed_seconds'},
            'Saved conditional equality extraction differs from fresh literal trace check')
    require(saved['status'] == 'PASS_CONDITIONAL_LITERAL_H7_EQUALITY_EXTRACTION'
            and saved['all_inputs_unchanged'] is True and saved['normalized_H'] == 51
            and saved['normalized_box_correction'] == 0 and saved['Y_point_transitivity'] is True
            and saved['exact_pair_tightness'] == dict(anchor=35008, pair=2176, total_count=3, root_offset=0),
            'Equality extraction does not give the required tight pair and two branches')
    equality_input = bind(saved['receipt']['path'], saved['receipt']['sha256'])
    original_equality = read(equality_input)
    z_four = {sum(1 << v for v in vs) for vs in it.combinations(range(6, 13), 4)}
    y_four = {sum(1 << v for v in vs) for vs in it.combinations(range(6), 4)}
    orbit = {6528, 6784}
    forbidden = z_four - orbit
    require(set(saved['forbidden_Z_internals']) == forbidden
            and set(saved['surviving_Z_internal_orbit']) == orbit
            and set(earlier['absent_core_four']) == y_four | forbidden,
            'Earlier exact exclusions do not discharge precisely the equality antecedents')
    require(isinstance(plan['branches'], list) and len(plan['branches']) == 2
            and {r['triangle_vertex'] for r in plan['branches']} == {0, 13}, 'Both triangle vertices are required')
    bind(HERE / 'degree17_full_projection_v5.py', V5)
    bind(HERE / 'replay_degree17_full_v5.py', REPLAY5)
    bind(HERE / 'degree17_full_phaseone_v5.py', PHASE5)
    branch_records = []
    for item in plan['branches']:
        require(set(item) == {'triangle_vertex', 'receipt', 'receipt_sha256', 'replay', 'replay_sha256'},
                'Malformed explicit branch binding')
        vertex = item['triangle_vertex']
        derived = next(r for r in saved['branches'] if r['triangle_vertex'] == vertex)
        require(not derived['fixed_sunflower_witnesses'], 'Unexpected direct fixed-sunflower branch')
        receipt_bound = bind(item['receipt'], item['receipt_sha256'])
        replay_bound = bind(item['replay'], item['replay_sha256'])
        data, evidence = read(receipt_bound), read(replay_bound)
        extras = derived['extra_members']
        selected = [6528] + extras
        require(data.get('status') == 0 and data.get('certificate_kind') == 'zero-infeasibility'
                and data.get('original_status') == 2 and data.get('source_sha256') == V5
                and data.get('certificate_producer_sha256') == PHASE5
                and data.get('kind') == 'P10-H7' and data.get('case') == 'IZ13'
                and data.get('root_degree') == data.get('point_cap') == 17
                and data.get('mu') == 41 and data.get('target_residuals') == 51
                and data.get('extra_members') == extras and data.get('selected_actual_members') == selected
                and data.get('represented_points') == derived['represented_points'], 'Wrong v5 equality branch')
        for key in ('empty_z', 'assigned_z', 'forbidden', 'forbid_four_core', 'degree_distributions',
                    'crowding_imports', 'h27_cliques', 'geometry', 'P10_internal_exclusion_receipts'):
            require(data.get(key) == original_equality.get(key), 'Branch changed equality premise: ' + key)
        raw_bound = bind(data['input_receipt_path'], data['input_receipt_sha256'])
        raw = read(raw_bound)
        require(raw.get('status') == 2, 'Phase-one input is not status2')
        changed = {'status', 'message', 'assurance', 'dual', 'primal_trace'}
        require(all(data.get(k) == v for k, v in raw.items() if k not in changed), 'Phase one changed original metadata')
        for dependency in data['imported_crowding_sources'].values():
            bind(dependency['path'], dependency['sha256'])
        branch_premise = dict(case='IZ13', actual_marker=6528, empty_z=False, assigned_z=None,
                              forbidden=sorted(forbidden), forbid_four_core=False, degree_distributions=False,
                              crowding_imports=True, h27_cliques=None, extra_members=extras,
                              selected_actual_members=selected, represented_points=derived['represented_points'])
        require(data['literal_premises'][-1] == branch_premise, 'Unexpected actuality or absence branch premise')
        identity = {key: data[key] for key in
                    ('source_sha256', 'imported_local43_sha256', 'structural_note_sha256', 'pool_note_sha256',
                     'imported_crowding_sources', 'P10_internal_exclusion_receipts', 'h27_cliques',
                     'extra_members', 'selected_actual_members', 'represented_points', 'kind', 'literal_premises')}
        require(value_hash(identity) == data['premise_sha256'], 'v5 premise fingerprint differs')
        dual, exact = data.get('dual', {}), evidence.get('exact_replay', {})
        require(all(type(dual.get(k)) is int for k in ('scale', 'H', 'correction', 'upper_numerator'))
                and dual['scale'] > 0 and dual['H'] + dual['correction'] == dual['upper_numerator'] < 0
                and dual.get('objective') == 'zero' and dual.get('below0') is True, 'Branch has no strict zero certificate')
        require(evidence.get('result') == 'PASS' and evidence.get('all_inputs_unchanged') is True
                and evidence.get('replayer_sha256') == REPLAY5
                and evidence.get('receipt_sha256') == receipt_bound['sha256']
                and evidence.get('source', {}).get('sha256') == V5
                and evidence.get('premise_sha256') == data['premise_sha256']
                and evidence.get('certificate_kind') == 'zero-infeasibility'
                and evidence.get('original_metadata_preserved') is True
                and all(exact.get(k) == dual[k] for k in ('scale', 'H', 'correction', 'upper_numerator'))
                and exact.get('target_numerator') == 0 and exact.get('G') == dual['upper_numerator']
                and exact.get('strict_exclusion') is True and exact.get('all_objective_coefficients_zero') is True,
                'Missing, failed or mismatched v5 exact replay')
        actual = evidence.get('extra_actual_member_validation', {})
        require(actual.get('required') is True and actual.get('extra_members') == extras
                and actual.get('selected_actual_members') == selected
                and actual.get('represented_points') == derived['represented_points']
                and actual.get('fixed_actual_member_count') == 20 and actual.get('fixed_anchor_rows_checked') == 520
                and all(actual.get(k) is True for k in ('trace_domain_checked', 'all_trace_boxes_checked',
                            'selected_membership_boxes_checked', 'root_only_offsets_checked'))
                and evidence.get('triangle_row_validation', {}).get('required') is True
                and evidence.get('marked_B4_validation', {}).get('required') is True
                and evidence['marked_B4_validation'].get('pruning_checked') is True
                and evidence.get('P10_exclusion_binding', {}).get('required') is True,
                'v5 replay lacks independent selected-family or actual-row validation')
        for dependency in evidence.get('dependencies', {}).values():
            bind(dependency['path'], dependency['sha256'])
        branch_records.append(dict(triangle_vertex=vertex, extra_members=extras, receipt=receipt_bound,
                                   replay=replay_bound, original=raw_bound, exact_gap=dual['upper_numerator'],
                                   scale=dual['scale']))
    for path, digest in tracked.items():
        require(sha(path) == digest, 'Bound input changed during coverage check')
    return dict(status='PASS_H7_INTERNAL_Z_EMPTY_EQUALITY_SPLIT_EXACT_BOUND', checker=checker,
                plan=plan_bound, ordinary_note=ordinary, kind='P10-H7',
                generic_checker=generic_bound, earlier_plan=earlier_plan,
                earlier_stage_records=earlier['records'], Y_empty_dependency=earlier['Y_empty_dependency'],
                equality_checker=equality_bound, equality_receipt=eq_bound, branches=branch_records,
                earlier_excluded_Z_four_sets=sorted(forbidden), equality_excluded_Z_orbit=sorted(orbit),
                excluded_Z_four_sets=sorted(z_four), all_35_Z_internals_absent=True,
                all_inputs_unchanged=True, elapsed_seconds=time.monotonic()-start,
                scope='Conditional ordinary H7 internal-Z emptiness:17 exact prior orbit exclusions plus independently reconstructed equality and both exact actual-member branches. No E4/E3 coverage, terminal or whole-H7/degree17 claim.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('plan', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    require(not args.output.exists(), 'Refusing to overwrite an H7 split coverage receipt')
    def timeout(_signum, _frame):
        raise TimeoutError('Thirty-second ordinary split binding deadline expired')
    signal.signal(signal.SIGALRM, timeout)
    signal.setitimer(signal.ITIMER_REAL, 30)
    result = check(args.plan)
    signal.setitimer(signal.ITIMER_REAL, 0)
    with args.output.open('x') as handle:
        json.dump(result, handle, indent=2, allow_nan=False)
        handle.write('\n')
    print(json.dumps(dict(status=result['status'], prior_orbits=len(result['earlier_stage_records']),
                          exact_split_leaves=len(result['branches']), output=str(args.output.resolve()),
                          elapsed_seconds=result['elapsed_seconds'])))


if __name__ == '__main__':
    main()
