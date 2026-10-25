#!/usr/bin/env python3
"""Tiny standard-library NO43 core census; no model import or solver.

The arbitrary-support reduction is in LOW14-Wagner-research.md. This file
enumerates only complete >=2-root-point cores, not complete SF4 families.
"""
import hashlib
import itertools as it
import json
from pathlib import Path
import time


HERE = Path(__file__).resolve().parent
PAIRS = tuple(it.combinations(range(4), 2))
EDGES = tuple((1 << a) | (1 << b) for a, b in it.combinations(range(4, 7), 2))
TYPES = ((0, 2, 3), (1, 1, 3), (1, 2, 2))
ROOT = 15


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def is_sf4(core):
    return all(a & b != a & c or a & b != b & c for a, b, c in it.combinations(core, 3))


def p_row(core):
    return [sum(s & ROOT == ((1 << a) | (1 << b)) for s in core) for a, b in PAIRS]


def main():
    start = time.monotonic()
    maps = []
    for r in it.permutations(range(4)):
        for e in it.permutations(range(4, 7)):
            perm = r + e
            maps.append(tuple(sum(1 << perm[v] for v in range(7) if s >> v & 1) for s in range(128)))
    totals = []
    grouped = {}
    for a, b, c in TYPES:
        # Pair order 01,02,03,12,13,23.
        ps = (a, b, c, c, b, a)
        raw = valid = 0
        for choices in it.product(*(tuple(it.combinations(EDGES, p)) for p in ps)):
            raw += 1
            core = tuple(sorted([ROOT] + [((1 << u) | (1 << v) | edge)
                for (u, v), edges in zip(PAIRS, choices) for edge in edges]))
            if len(core) != 11 or len(set(core)) != 11:
                raise RuntimeError('incorrect complete-core member count')
            if not is_sf4(core):
                continue
            valid += 1
            if any(sum(s >> v & 1 for s in core) != 6 for v in range(4)):
                raise RuntimeError('root core degree must be six')
            if any((u & v) == (1 << i) for i in range(4) for u, v in it.combinations(core, 2)):
                raise RuntimeError('B4 near-intersection condition failed')
            images = {tuple(sorted(mp[s] for s in core)) for mp in maps}
            canonical = min(images)
            record = grouped.setdefault(canonical, dict(type=list((a, b, c)),
                canonical_core=list(canonical), p_row=p_row(canonical),
                orbit_size_under_S4_times_S3=len(images), representative_domain_count=0))
            record['representative_domain_count'] += 1
        totals.append(dict(type=list((a, b, c)), raw=raw, valid=valid))
    records = []
    for i, (core, record) in enumerate(sorted(grouped.items())):
        record['id'] = f'NO43_{i:03d}'
        record['root_points'] = list(range(4))
        record['exterior_triangle'] = [4, 5, 6]
        record['core_degrees'] = [sum(s >> v & 1 for s in core) for v in range(7)]
        record['root_singletons'] = [8, 8, 8, 8]
        record['root_neighbourhood'] = 43
        records.append(record)
    result = dict(schema='cap14-N43-seven-point-core-census-v1',
        assurance='Exact finite core census conditional on the ordinary arbitrary-support reduction; no completion exclusion, solver, model reconstruction, or Lean.',
        literal_premises=[
            'F is finite simple SF4 and has size68, global point cap14, and all actual neighbourhoods at least41.',
            'All exact singleton counts are at most8, as derived by the ordinary cap14 P9 exclusion.',
            'The actual root0123 has neighbourhood43; its complete >=2-root-point core has the seven-point form proved in LOW14-Wagner-research.md.',
            'Root points have global degree14, singleton8, and no exact triple-root trace; arbitrary residual exterior support is allowed.',
        ],
        source_sha256=sha(__file__), ordinary_bridge_sha256=sha(HERE/'LOW14-Wagner-research.md'),
        root_pairs=[list(p) for p in PAIRS], exterior_edges=list(EDGES),
        action='All24 permutations of root points and all6 permutations of the exterior triangle; entire core transported.',
        totals=totals, raw_assignments=sum(t['raw'] for t in totals),
        valid_representative_assignments=sum(t['valid'] for t in totals),
        canonical_records=len(records), records=records, seconds=time.monotonic()-start)
    output = HERE/'LOW14-N43-core-census.json'
    with output.open('x') as stream:
        json.dump(result, stream, indent=2)
        stream.write('\n')
    print(json.dumps({k: result[k] for k in ('raw_assignments', 'valid_representative_assignments',
        'canonical_records', 'totals', 'seconds', 'source_sha256')}, separators=(',', ':')))


if __name__ == '__main__':
    main()
