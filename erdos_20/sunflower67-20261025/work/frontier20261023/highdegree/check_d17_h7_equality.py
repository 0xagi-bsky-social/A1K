#!/usr/bin/env python3
"""Independent literal 15-row H7 equality extraction; no model import or build.

Checks only 1093 core traces and the literal S6/S7 automorphism groups. This
does not replay the whole LP or establish the previous orbit exclusions.
Its bound and forced two-branch conclusion retain those explicit premises.
"""
import argparse
import hashlib
import itertools as it
import json
from pathlib import Path
import signal
import time

HERE = Path(__file__).resolve().parent
RECEIPT = HERE / 'degree17_full/P10-H7-IZ13-internal-Z-stage2-v4-9ff2bf3fd06c.json'
RECEIPT_SHA = '0d4b5004a86f70dfe0c90c02dafd3346499f4c31e6e84fb76589bf239ae3fc68'
V4_SHA = 'a1beae56f60205a48442a1c6a31d2148557443511fb119a1936ffda8578bebf2'


def require(value, message):
    if not value:
        raise ValueError(message)


def mask(points):
    return sum(1 << v for v in points)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def value_hash(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'),
                                     allow_nan=False).encode()).hexdigest()


def check():
    started = time.monotonic()
    tracked = {}

    def bind(path, digest=None):
        path = Path(path).resolve()
        actual = sha(path)
        require(digest is None or digest == actual, 'Changed input: ' + str(path))
        require(path not in tracked or tracked[path] == actual, 'Input changed during check')
        tracked[path] = actual
        return dict(path=str(path), sha256=actual)

    checker = bind(__file__)
    receipt = bind(RECEIPT, RECEIPT_SHA)
    source = bind(HERE / 'degree17_full_projection_v4.py', V4_SHA)
    note = bind(HERE / 'D17-H7-equality-extra-members.md')
    data = json.loads(RECEIPT.read_text())
    require(data.get('kind') == 'P10-H7' and data.get('case') == 'IZ13'
            and data.get('status') == 0 and data.get('source_sha256') == V4_SHA
            and data.get('root_degree') == 17 and data.get('point_cap') == 17
            and data.get('mu') == 41 and data.get('target_residuals') == 51
            and data.get('empty_z') is False and data.get('assigned_z') is None
            and data.get('forbid_four_core') is False
            and data.get('degree_distributions') is False
            and data.get('crowding_imports') is True and data.get('h27_cliques') is None,
            'Wrong equality receipt scope')
    p10 = tuple(frozenset(map(int, t)) for t in
                '012 015 023 034 045 124 134 135 235 245'.split())
    h7 = tuple(frozenset(map(int, t)) for t in
               '023 024 034 124 134 015 016'.split())
    y, z = mask(range(6)), mask(range(6, 13))
    link = tuple(map(mask, p10)) + tuple(mask(v + 6 for v in t) for t in h7)
    star = tuple(t | (1 << 15) for t in link)
    marker = mask((7, 8, 11, 12))
    fixed = star + (marker,)
    require(not any(a & b == a & c == b & c for a, b, c in it.combinations(fixed, 3)),
            'Literal actual family is already a sunflower')
    require(sorted(data['geometry']['link']) == sorted(link)
            and data['geometry']['Y'] == list(range(6))
            and data['geometry']['Z'] == list(range(6, 13))
            and data['geometry']['root'] == 15, 'Wrong literal complete root link')
    ay = [p for p in it.permutations(range(6))
          if {frozenset(p[v] for v in t) for t in p10} == set(p10)]
    az = [p for p in it.permutations(range(7))
          if {frozenset(p[v] for v in t) for t in h7} == set(h7)]
    require(len(ay) == 60 and len(az) == 4 and {p[0] for p in ay} == set(range(6)),
            'Incorrect component automorphisms or Y point transitivity')
    orbit = {mask(p[v-6] + 6 for v in (7, 8, 11, 12)) for p in az}
    require(orbit == {6528, 6784} and data['geometry']['records']['IZ13'] ==
            dict(marker=6528, category='internal-Z', orbit_size=2, orbit=[6528, 6784]),
            'Wrong surviving internal orbit')
    forbidden = {mask(vs) for vs in it.combinations(range(6, 13), 4)} - orbit
    require(data['forbidden'] == sorted(forbidden), 'Antecedent is not exactly the other17 Z orbits')
    for item in data['imported_crowding_sources'].values():
        bind(item['path'], item['sha256'])
    for filename, field in (('D18-structural-tools.md', 'structural_note_sha256'),
                            ('D18-pool-research.md', 'pool_note_sha256')):
        bind(HERE / filename, data[field])
    local43 = HERE.parents[1] / 'frontier20261020/prior-art68/repository/companion/upstream/MU42/scripts/local43.py'
    bind(local43, data['imported_local43_sha256'])
    for filename, item in data['P10_internal_exclusion_receipts'].items():
        bind(HERE / 'degree17' / filename, item['sha256'])
    identity = {key: data[key] for key in
                ('source_sha256', 'imported_local43_sha256', 'structural_note_sha256',
                 'pool_note_sha256', 'imported_crowding_sources',
                 'P10_internal_exclusion_receipts', 'h27_cliques', 'kind', 'literal_premises')}
    require(value_hash(identity) == data['premise_sha256'], 'Receipt premise fingerprint changed')
    traces = tuple(mask(vs) for k in range(5) for vs in it.combinations(range(13), k))
    zero_y = {s for s in traces if s.bit_count() == 4 and s & y == s}
    zero_sf = {s for s in traces if any(s & a == s & b == a & b
               for a, b in it.combinations(fixed, 2) if not (a & (1 << 15) and b & (1 << 15)))}
    zero = forbidden | zero_y | zero_sf
    expected_labels = [['incidence', mask(t)] for t in p10] + [
        ['incidence', mask((8, 9, 10))],
        ['exact-anchor', mask((15, 6, 7, 11)), mask((7, 11))],
        ['imported-crowding26', mask((15, 6, 7, 11)), [7, 11, 15]],
        ['exact-anchor', mask((15, 6, 7, 12)), mask((12,))],
        ['triangle-path-hub-degree-minus-completions15', 6]]
    dual = data['dual']
    require(type(dual['scale']) is int and dual['scale'] > 0 and dual['eq'] == []
            and [item[2] for item in dual['ineq']] == expected_labels
            and all(type(item[1]) is int and item[1] == dual['scale'] for item in dual['ineq']),
            'Expected exactly15 unit-weight trace rows and no equality weights')
    rows = []
    for label in expected_labels:
        kind = label[0]
        if kind == 'incidence':
            u = label[1]
            pred = lambda s, u=u: s & u == u
            rhs = 2 - sum(pred(b) for b in star)
        elif kind == 'exact-anchor':
            a, u = label[1:]
            pred = lambda s, a=a, u=u: s & a == u
            rhs = {1: 10, 2: 3}[u.bit_count()] - sum(pred(b) for b in star)
        elif kind == 'imported-crowding26':
            a, singletons = label[1], tuple(1 << v for v in label[2])
            pred = lambda s, a=a, singletons=singletons: s & a in singletons
            rhs = 26 - sum(pred(b) for b in star)
        elif kind == 'triangle-path-hub-degree-minus-completions15':
            v = label[1]
            edges = [t ^ (1 << v) for t in link if t >> v & 1]
            completions = {s for s in traces if s.bit_count() == 4 and s & z == s
                           and s >> v & 1 and all((s ^ (1 << v)) & e for e in edges)}
            require(len(completions) == 3, 'Wrong literal hub cover completions')
            pred = lambda s, v=v, completions=completions: bool(s >> v & 1) and s not in completions
            rhs = 15 - sum(b >> v & 1 for b in star)
        else:
            raise ValueError('Unsupported row')
        rows.append((label, rhs, pred))
    q = {s: sum(pred(s) for _, _, pred in rows) for s in traces}
    require(sum(rhs for _, rhs, _ in rows) == 51 and len(traces) == 1093
            and len(zero) == 517 and marker not in zero and q[marker] == 1
            and all(q[s] >= 1 for s in traces if s not in zero),
            'Literal trace inequality does not prove residual<=51')
    hi = {s: 0 if s in zero else {0: 27, 1: 17, 2: 6, 3: 2, 4: 1}[s.bit_count()] for s in traces}
    correction = sum(max(int(s == marker) * (1 - q[s]), hi[s] * (1 - q[s])) for s in traces)
    require(correction == 0 and dual['correction'] == 0
            and dual['H'] == dual['upper_numerator'] == 51 * dual['scale'],
            'Saved integer diagnostic differs from independent literal inequality')
    require(mask((7, 8, 11, 9)) in forbidden and mask((7, 8, 11, 10)) in forbidden,
            'The two other-core triangle vertices were not already excluded')
    branches = []
    for vertex in (0, 13):
        extras = [mask((7, 8, 11, vertex)), mask((7, 11, 12, vertex))]
        all_fixed = fixed + tuple(extras)
        witnesses = [[a, b, c] for a, b, c in it.combinations(all_fixed, 3)
                     if a & b == a & c == b & c]
        branches.append(dict(triangle_vertex=vertex, extra_members=sorted(extras),
                             represented_points=list(range(13 + int(vertex == 13))),
                             fixed_sunflower_witnesses=witnesses))
    for path, digest in tracked.items():
        require(sha(path) == digest, 'Input changed during check: ' + str(path))
    return dict(status='PASS_CONDITIONAL_LITERAL_H7_EQUALITY_EXTRACTION', checker=checker,
                ordinary_note=note, receipt=receipt, producer=source,
                premise_sha256=data['premise_sha256'], traces=len(traces), zero_traces=len(zero),
                eligible_traces=len(traces)-len(zero),
                eligible_coefficient_counts={str(k): sum(q[s] == k for s in traces if s not in zero)
                                             for k in sorted(set(q.values()))},
                integer_scale=dual['scale'], normalized_H=51, normalized_box_correction=0,
                normalized_rows=[dict(label=label, rhs=rhs, weight=1) for label, rhs, _ in rows],
                exact_pair_tightness=dict(anchor=35008, pair=2176, total_count=3, root_offset=0),
                surviving_Z_internal_orbit=sorted(orbit), forbidden_Z_internals=sorted(forbidden),
                Y_point_transitivity=True, branches=branches, all_inputs_unchanged=True,
                elapsed_seconds=time.monotonic()-started,
                scope='Independent trace-only integer inequality and finite two-branch geometry. Prior12 P10 component exclusions, other17 Z-orbit exclusions and ordinary row theorems remain explicit premises; no LP/model import, solver, local-catalogue replay or complete H7 closure.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    output = args.output or HERE / 'degree17_full/H7-IZ13-equality-extraction.json'
    require(not output.exists(), 'Refusing to overwrite an existing output')
    def timeout(_signum, _frame):
        raise TimeoutError('Twenty-second literal equality check deadline expired')
    signal.signal(signal.SIGALRM, timeout)
    signal.setitimer(signal.ITIMER_REAL, 20)
    result = check()
    signal.setitimer(signal.ITIMER_REAL, 0)
    with output.open('x') as handle:
        json.dump(result, handle, indent=2, allow_nan=False)
        handle.write('\n')
    print(json.dumps(dict(status=result['status'], H=result['normalized_H'],
                          correction=result['normalized_box_correction'],
                          output=str(output.resolve()), elapsed_seconds=result['elapsed_seconds'])))


if __name__ == '__main__':
    main()
