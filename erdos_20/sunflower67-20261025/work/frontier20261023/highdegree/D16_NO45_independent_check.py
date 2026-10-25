#!/usr/bin/env python3
"""Independent bounded integer reconstruction of the N45 scalar signatures.

Reverse enumeration starts from pair/triple counts, derives each singleton
ceiling from degree16, then enumerates only deficits from those ceilings.
No solver, geometry realization or exterior-support enumeration is used.
"""
import hashlib
import itertools as it
import json
from pathlib import Path
import signal
import time

HERE = Path(__file__).resolve().parent
EDGES = tuple(it.combinations(range(4), 2))
PERMS = tuple(it.permutations(range(4)))
SIG8 = {((0, 1), (2, 1), (2, 1)), ((1, 1), (1, 1), (2, 1)),
        ((1, 1), (2, 0), (2, 1)), ((0, 1), (3, 0), (3, 0))}
SIG7 = {((1, 1), (3, 0), (3, 0))}


def main():
    start = time.monotonic()
    def deadline(*_):
        raise TimeoutError('Independent scalar census exceeded one second')
    signal.signal(signal.SIGALRM, deadline)
    signal.setitimer(signal.ITIMER_REAL, 1.0)
    counts = [0, 0, 0]
    rows = set()
    for p in it.product(range(4), repeat=6):
        r = tuple(sum(p[e] for e, ij in enumerate(EDGES) if i in ij) for i in range(4))
        for t in it.product((0, 1), repeat=4):
            T = sum(t)
            S = 44-sum(p)-T
            if not 28+T <= S <= 32:
                continue
            upper = tuple(min(8, 15-r[i]-T+t[i]) for i in range(4))
            if min(upper) < 0 or sum(upper) < S:
                continue
            deficit = sum(upper)-S
            for z0 in range(min(deficit, upper[0])+1):
                for z1 in range(min(deficit-z0, upper[1])+1):
                    for z2 in range(min(deficit-z0-z1, upper[2])+1):
                        z3 = deficit-z0-z1-z2
                        if z3 > upper[3]:
                            continue
                        s = tuple(u-z for u, z in zip(upper, (z0, z1, z2, z3)))
                        if tuple(sorted(s)) != s:
                            continue
                        d = tuple(1+s[i]+r[i]+T-t[i] for i in range(4))
                        counts[0] += 1
                        if any(1+p[e]+sum(t[z] for z in range(4) if z not in ij)>6
                               for e, ij in enumerate(EDGES)):
                            continue
                        if any(s[i]==8 and r[i]>6 for i in range(4)):
                            continue
                        if any(p[e]==3 and any(t[i] and s[j]==8 for i,j in (ij, ij[::-1]))
                               for e,ij in enumerate(EDGES)):
                            continue
                        if any(t[i] and r[i]>4 and all(s[j]==8 for j in range(4) if j!=i)
                               for i in range(4)):
                            continue
                        if all(z==8 for z in s) and all(z>=5 for z in r):
                            continue
                        counts[1] += 1
                        signatures = [tuple(sorted((p[EDGES.index(tuple(sorted((i,j))))],t[j])
                                                   for j in range(4) if j!=i)) for i in range(4)]
                        if any(d[i]==16 and signatures[i] not in
                               (SIG8 if s[i]==8 else SIG7 if s[i]==7 else set()) for i in range(4)):
                            continue
                        counts[2] += 1
                        orbit = []
                        for perm in PERMS:
                            # New labels read their old coordinates through perm.
                            pp = tuple(p[EDGES.index(tuple(sorted((perm[i],perm[j]))))] for i,j in EDGES)
                            orbit.append(pp+tuple(t[i] for i in perm)+tuple(s[i] for i in perm))
                        rows.add(min(orbit))
    signal.setitimer(signal.ITIMER_REAL, 0)
    expected = {
        (0,2,2,2,2,0,1,1,1,1,8,8,8,8),
        (1,1,2,2,1,1,1,1,1,1,8,8,8,8),
    }
    if counts != [2054,164,6] or rows != expected:
        raise ValueError('Scalar reconstruction disagrees with the stated exhaustive outcome')
    record = dict(schema='cap16-N45-independent-scalar-v1', result='PASS',
                  source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  counts=counts, orbit_count=len(rows), canonical_rows=[list(r) for r in sorted(rows)],
                  seconds=time.monotonic()-start,
                  assurance='Independent reverse enumeration of necessary scalar signatures only; the literal I8 signatures and ordinary geometric exclusions remain separately checked premises.')
    target = HERE/'D16-NO45-independent-scalar.json'
    if target.exists():
        raise FileExistsError(target)
    target.write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record))

if __name__=='__main__':
    main()
