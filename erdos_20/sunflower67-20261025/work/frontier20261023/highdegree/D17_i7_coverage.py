#!/usr/bin/env python3
"""Small independent finite I7 census; no model, solver, or upstream imports.

The arbitrary-support reduction and uniqueness of the seven-point type remain
ordinary premises.  This checks all C(20,7) six-point candidates directly,
then compares literal permutation orbits with the imported eight templates.
"""
import hashlib
import itertools as it
import json
import pathlib
import time

HERE = pathlib.Path(__file__).resolve().parent
PRIOR = HERE.parents[1] / 'frontier20261020/prior-art68'
CERT = PRIOR / 'repository/companion/terminal/r16/results/seven_certificate.json'


def mask(vs):
    return sum(1 << v for v in vs)


def sunflower(a, b, c):
    return a & b == a & c == b & c


def check():
    start = time.monotonic()
    certificate = json.loads(CERT.read_text())
    rows = certificate['rows']
    if certificate['format'] != 'E20_I7_catalogue_v1' or [r['id'] for r in rows] != list(range(8)):
        raise ValueError('Unexpected imported catalogue format or eight-type coverage')
    triples = tuple(mask(t) for t in it.combinations(range(6), 3))
    index = {t: i for i, t in enumerate(triples)}
    disjoint_pairs = {pair for pair in it.combinations(range(20), 2)
                      if not triples[pair[0]] & triples[pair[1]]}
    bad = {abc for abc in it.combinations(range(20), 3)
           if sunflower(*(triples[j] for j in abc))}
    actual, visited = set(), 0
    for ids in it.combinations(range(20), 7):
        visited += 1
        if any(pair in disjoint_pairs for pair in it.combinations(ids, 2)):
            continue
        if any(abc in bad for abc in it.combinations(ids, 3)):
            continue
        actual.add(mask(ids))
    covered, orbit_sizes = set(), []
    mixed_count = 0
    for i, row in enumerate(rows):
        size = 6 if i < 7 else 7
        fam = tuple(mask(block) for block in row['blocks'])
        support = 0
        for t in fam:
            support |= t
        if len(fam) != 7 or len(set(fam)) != 7 or support != (1 << size) - 1:
            raise ValueError('Template is not seven distinct triples on its support')
        if any(t.bit_count() != 3 for t in fam) or any(not a & b for a, b in it.combinations(fam, 2)):
            raise ValueError('Template not intersecting triple-uniform')
        if any(sunflower(a, b, c) for a, b, c in it.combinations(fam, 3)):
            raise ValueError('Template contains a sunflower')
        if i < 7:
            orbit = {mask(index[mask(p[v] for v in range(6) if t >> v & 1)] for t in fam)
                     for p in it.permutations(range(6))}
            if covered & orbit or len(orbit) != row['labelled_count']:
                raise ValueError('Template orbit overlap or wrong size')
            covered |= orbit
            orbit_sizes.append(len(orbit))
        else:
            qminus = {mask(t) for t in ((0, 2, 3), (0, 2, 4), (0, 3, 4),
                                      (1, 2, 4), (1, 3, 4), (0, 1, 5), (0, 1, 6))}
            if set(fam) != qminus:
                raise ValueError('Wrong analytic seven-point model')
        allowed = {mask(t) for t in row['mixed_allowed']}
        forbidden = {mask(r['trace']): r['witness'] for r in row['mixed_forbidden']}
        domain = {mask(t) for k in (1, 2) for t in it.combinations(range(size), k)}
        if allowed & forbidden.keys() or allowed | forbidden.keys() != domain:
            raise ValueError('Incomplete mixed-trace partition')
        for trace in domain:
            mixed_count += 1
            witnesses = [(a, b) for a, b in it.combinations(range(7), 2)
                         if sunflower(fam[a], fam[b], trace)]
            if trace in allowed:
                if witnesses:
                    raise ValueError('Allowed mixed trace has a forbidden pair')
            elif tuple(forbidden[trace]) not in witnesses:
                raise ValueError('Invalid actual-pair trace witness')
    if visited != 77520 or actual != covered or len(actual) != 1860:
        raise ValueError('Independent six-point exhaustive census mismatch')
    return dict(status='PASS_INDEPENDENT_FINITE_I7_COVERAGE',
                six_point_candidates=visited, labelled_six_point_families=len(actual),
                orbit_sizes=orbit_sizes, seven_point_types=1,
                mixed_traces=mixed_count, seconds=time.monotonic() - start,
                source_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
                imported_certificate_sha256=hashlib.sha256(CERT.read_bytes()).hexdigest(),
                ordinary_premises=['Every intersecting SF3 seven-family has support at most seven.',
                                   'The degree-one/degree-five ordinary reduction leaves only H7 on seven points.'],
                assurance='Independent finite census of stated support domain; not a proof of the ordinary support reduction, a solver run, or Lean.')


if __name__ == '__main__':
    result = check()
    output = HERE / 'D17-i7-coverage.json'
    if output.exists():
        raise FileExistsError('Refusing to overwrite existing independent coverage receipt')
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
