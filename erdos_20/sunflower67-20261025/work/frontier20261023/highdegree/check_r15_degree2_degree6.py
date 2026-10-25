#!/usr/bin/env python3
"""Literal arbitrary-support obstruction for the forced degree2/degree6 motif.

Standard-library finite diagnostic, not Lean. Every rejection carries two
literal earlier triples forming a sunflower with the tested triple, or a
literal seven-disjoint-triples witness. Exterior labels are padded by three
only for the single next triple; no ambient support bound is assumed.
"""
import argparse
import hashlib
import itertools as it
import json
import time
from pathlib import Path


def sunflower(a, b, c):
    return a & b == a & c == b & c


def rejection(fam):
    for a, b, c in it.combinations(fam, 3):
        if sunflower(a, b, c):
            return {'kind': 'sunflower', 'members': [sorted(a), sorted(b), sorted(c)]}
    for a in fam:
        disjoint = [b for b in fam if not a & b]
        if len(disjoint) >= 7:
            return {'kind': 'rho_above_six', 'anchor': sorted(a),
                    'members': [sorted(b) for b in disjoint[:7]]}
    return None


def triangle_lifts(hub, triad):
    return [frozenset((hub,) + edge) for edge in it.combinations(triad, 2)]


def run():
    start = time.monotonic()
    rows = []
    valid = extensions = 0
    for overlap in range(4):
        t = (4, 5, 6)
        d = tuple(range(4, 4 + overlap)) + tuple(range(7, 10 - overlap))
        used = sorted(set(t) | set(d))
        first = max(used) + 1
        # Any new E labels are renamed in order of first appearance.
        for e in it.combinations(used + list(range(first, first + 3)), 3):
            new = sorted(set(e) - set(used))
            if new != list(range(first, first + len(new))):
                continue
            fam = [frozenset(z) for z in ((0, 1, 2), (0, 1, 3), (1, 2, 3))]
            fam += triangle_lifts(1, t) + triangle_lifts(2, d) + triangle_lifts(3, e)
            if len(set(fam)) != 12:
                raise ValueError('motif lost twelve distinct triples')
            why = rejection(fam)
            row = {'T': list(t), 'D': list(d), 'E': list(e), 'rejection': why}
            if why is None:
                valid += 1
                support = sorted(set().union(*fam))
                exterior = max(support) + 1
                allowed = [v for v in support if v not in (0, 1, 2, 3)]
                candidates = it.combinations(allowed + list(range(exterior, exterior + 3)), 3)
                witnesses = []
                for candidate in candidates:
                    c = frozenset(candidate)
                    witness = next(((a, b) for a, b in it.combinations(fam, 2)
                                    if sunflower(a, b, c)), None)
                    if witness is None:
                        extensions += 1
                        witnesses.append({'candidate': list(candidate), 'open': True})
                    else:
                        witnesses.append({'candidate': list(candidate),
                                          'conflict': [sorted(z) for z in witness]})
                row['extension_witnesses'] = witnesses
            rows.append(row)
            if time.monotonic() - start > 5:
                raise TimeoutError('five-second diagnostic ceiling exceeded')
    return {'schema': 'r15-degree2-degree6-literal-v1',
            'status': 'PASS' if extensions == 0 else 'OPEN',
            'normalized_motifs': len(rows), 'valid_partial_motifs': valid,
            'unobstructed_thirteenth_triples': extensions,
            'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'rows': rows, 'seconds': time.monotonic() - start,
            'assurance': 'certificate-diagnostic; arbitrary-support motif normalization is an ordinary bridge, not Lean.'}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    result = run()
    with args.output.open('x') as out:
        json.dump(result, out, indent=2)
        out.write('\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'rows'}))
    if result['status'] != 'PASS':
        raise SystemExit(2)


if __name__ == '__main__':
    main()
