#!/usr/bin/env python3
"""Exact bounded diagnostic for the Abbott-Hanson 27-set construction.

No solver, floating arithmetic, random search, or external executable is used.
This computes finite data; it does not supply a Lean kernel certificate.
"""
from itertools import combinations, product
from functools import lru_cache
from collections import Counter
from pathlib import Path
import hashlib, json, time

HERE = Path(__file__).resolve().parent
START = time.monotonic()
TIME_LIMIT = 60

def points(x):
    return [i for i in range(9) if (x >> i) & 1]

def sf(a, b, c):
    return (a & b) == (a & c) == (b & c)

A = sorted(sum(1 << x for x in (*p, *q))
           for i, j in combinations(range(3), 2)
           for p in combinations(range(3*i, 3*i+3), 2)
           for q in combinations(range(3*j, 3*j+3), 2))
assert len(set(A)) == 27
assert all(a.bit_count() == 4 for a in A)
assert all(a & b for a, b in combinations(A, 2))
assert not any(sf(a, b, c) for a, b, c in combinations(A, 3))

def min_cover(edges, forced=0):
    adjacency = [0] * len(A)
    for u, v in edges:
        adjacency[u] |= 1 << v
        adjacency[v] |= 1 << u

    @lru_cache(None)
    def solve(remaining):
        if time.monotonic() - START > TIME_LIMIT:
            raise TimeoutError('Probe deadline exceeded; no completion claim allowed')
        choices = [(u, adjacency[u] & remaining) for u in range(len(A))
                   if (remaining >> u) & 1 and adjacency[u] & remaining]
        if not choices:
            return 0
        u, neighbors = max(choices, key=lambda z: z[1].bit_count())
        v = (neighbors & -neighbors).bit_length()-1
        left = (1 << u) | solve(remaining & ~(1 << u))
        right = (1 << v) | solve(remaining & ~(1 << v))
        return min((left, right), key=lambda z: (z.bit_count(), z))

    answer = forced | solve(((1 << len(A))-1) & ~forced)
    assert all(answer & ((1 << u) | (1 << v)) for u, v in edges)
    return answer, solve.cache_info().currsize

records=[]
for counts in product(range(4), repeat=3):
    if not counts[0] >= counts[1] >= counts[2]:
        continue
    if not 1 <= sum(counts) <= 4 or counts == (2, 2, 0):
        continue
    trace = sum(1 << (3*i+j) for i in range(3) for j in range(counts[i]))
    blockers = [(i, j) for i, j in combinations(range(len(A)), 2)
                if sf(A[i], A[j], trace)]
    assert blockers
    cover, states = min_cover(blockers)
    forced = sum(1 << i for i, a in enumerate(A) if not a & trace)
    icover, istates = min_cover(blockers, forced)
    i, j = min(blockers, key=lambda ij: ((A[ij[0]] & A[ij[1]]).bit_count(),
                                        points(A[ij[0]]), points(A[ij[1]])))
    records.append(dict(profile=counts, trace=points(trace),
                        first=points(A[i]), second=points(A[j]), core=points(A[i]&A[j]),
                        blocker_count=len(blockers), deletion_minimum=cover.bit_count(),
                        deletion_witness=[points(A[x]) for x in range(27) if cover>>x&1],
                        intersecting_deletion_minimum=icover.bit_count(),
                        intersecting_forced_deletions=forced.bit_count(),
                        branching_states=states, intersecting_branching_states=istates))

traces=[]
for k in range(5):
    for t in combinations(range(9), k):
        mask=sum(1 << i for i in t)
        # Four-set traces already in A represent the same member, not an extension.
        if mask in A:
            continue
        blockers=[(i,j) for i,j in combinations(range(27),2) if sf(A[i],A[j],mask)]
        traces.append(dict(trace=list(t),blocker_count=len(blockers)))
        assert bool(blockers) == bool(t)

result=dict(evidence_grade='certificate-diagnostic',
            source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            family=[points(a) for a in A],
            family_size=27, universe_size=9,
            checked_traces_including_27_existing_sets=sum(1 for x in range(512) if x.bit_count()<=4),
            nonmember_traces=len(traces), admissible_nonmember_traces=[x['trace'] for x in traces if not x['blocker_count']],
            orbits=records, trace_records=traces,
            runtime_seconds=time.monotonic()-START,
            scope='All traces of four-sets on this fixed nine-point support, with arbitrary exterior points. No extremal-27 classification.')
(HERE/'trace_probe.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('family','trace_records')},indent=2))
