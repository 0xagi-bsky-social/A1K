#!/usr/bin/env python3
"""Exact finite diagnostic for the ordinary AHS deletion-stability proof.

Independent Python implementation; no numerical solver or imported data.
Checks all 101584 omitted subsets of at most five of the 27 AHS blocks.
It also emits the small local blocker-graph witnesses used in the proof.
This is not a Lean kernel certificate.
"""
from collections import Counter
from itertools import combinations
from pathlib import Path
import hashlib
import json
import math
import time

HERE = Path(__file__).resolve().parent
START = time.monotonic()
DEADLINE = 60
PARTS = (7, 56, 448)
PAIRS = tuple(tuple(p ^ (1 << i) for i in range(9) if p >> i & 1)
              for p in PARTS)
A = tuple(sorted(p | q for i, j in combinations(range(3), 2)
                 for p in PAIRS[i] for q in PAIRS[j]))
assert len(A) == len(set(A)) == 27
INDEX = {a: i for i, a in enumerate(A)}

def sf(a, b, t):
    return a & b == a & t == b & t

def profile(t):
    return tuple(sorted(((t & p).bit_count() for p in PARTS), reverse=True))

def blockers(t):
    return tuple((1 << i) | (1 << j) for i, j in combinations(range(27), 2)
                 if sf(A[i], A[j], t))

def matching(edges, need):
    if not need:
        return ()
    if len(edges) < need:
        return None
    for n, edge in enumerate(edges):
        tail = matching(tuple(e for e in edges[n+1:] if not e & edge), need-1)
        if tail is not None:
            return (edge,) + tail
    return None

def points(mask):
    return [i for i in range(9) if mask >> i & 1]

traces = []
for t in range(1, 512):
    if t.bit_count() > 4 or t in INDEX:
        continue
    containing = sum(1 << i for i, a in enumerate(A) if a & t == t)
    traces.append((t, profile(t), blockers(t), containing))
assert len(traces) == 228
profiles = sorted(set(p for _, p, _, _ in traces))
assert len(profiles) == 8
local = []
for prof in profiles:
    t, _, edges, _ = next(record for record in traces if record[1] == prof)
    if prof in ((1, 0, 0), (1, 1, 0), (1, 1, 1), (3, 0, 0), (3, 1, 0)):
        witness = matching(edges, 6)
        assert witness is not None
        kind = 'contains six disjoint blocker edges'
    elif prof == (2, 1, 1):
        witness = matching(edges, 5)
        assert len(edges) == 5 and witness is not None
        kind = 'exactly five disjoint blocker edges'
    else:
        witness = ()
        kind = 'K3,3' if prof == (2, 0, 0) else 'disjoint union K1,3 and K2'
    local.append(dict(profile=prof, trace=points(t), kind=kind,
                      edges=[[points(A[i]) for i in range(27) if e >> i & 1]
                             for e in edges],
                      six_matching_witness=[[points(A[i]) for i in range(27)
                                             if e >> i & 1] for e in witness]))

# Check the claimed exact blocker graphs for EVERY small-profile trace,
# independently of the representative/matching classification above.
for t, prof, edges, _ in traces:
    if prof not in ((2, 0, 0), (2, 1, 0), (2, 1, 1)):
        assert matching(edges, 6) is not None
        continue
    i = next(i for i in range(3) if (t & PARTS[i]).bit_count() == 2)
    p = t & PARTS[i]
    j, k = [g for g in range(3) if g != i]
    if prof == (2, 1, 0) and not t & PARTS[j]:
        j, k = k, j
    def block(q):
        return 1 << INDEX[p | q]
    if prof == (2, 0, 0):
        expected = {block(q) | block(r) for q in PAIRS[j] for r in PAIRS[k]}
    elif prof == (2, 1, 0):
        b = t & PARTS[j]
        b0 = PARTS[j] ^ b
        b1, b2 = [q for q in PAIRS[j] if q & b]
        expected = {block(b1) | block(b2)} | {block(b0) | block(r) for r in PAIRS[k]}
    else:
        assert len(edges) == 5 and matching(edges, 5) is not None
        continue
    assert set(edges) == expected

# Each vertex in K3,3,3 is one pair in one triple. Its two masks are its
# incident rows to the other parts. Each AHS block is one graph edge.
rows = []
piece_masks = []
for i in range(3):
    for p in PAIRS[i]:
        rows.append(tuple(sum(1 << INDEX[p | q] for q in PAIRS[j])
                          for j in range(3) if j != i))
for i, j in combinations(range(3), 2):
    piece_masks.append(sum(1 << INDEX[p | q] for p in PAIRS[i] for q in PAIRS[j]))

def evaluate(D):
    direct = 0
    q211 = 0
    for t, prof, edges, containing in traces:
        if any(not D & edge for edge in edges):
            continue
        assert prof in ((2, 0, 0), (2, 1, 0), (2, 1, 1))
        if prof == (2, 0, 0):
            assert containing & ~D
            direct += 3
        elif prof == (2, 1, 0):
            direct += 1 if containing & ~D else 2
        else:
            direct += 1
            q211 += 1
    B = 0
    full = 0
    correction = 0
    for left, right in rows:
        k, l = (D & left).bit_count(), (D & right).bit_count()
        assert (k, l) != (3, 3)
        B += k * (k-1) + l * (l-1)
        full += int(k == 3) + int(l == 3)
        correction += (l*(3-l) if k == 3 else 0) + (k*(3-k) if l == 3 else 0)
    structural = B + 3*full + correction + q211
    assert structural == direct
    assert B <= 12 and full <= 2
    if q211:
        assert sorted((D & p).bit_count() for p in piece_masks) == [1, 2, 2]
        assert full == 0 and B <= 4 and q211 <= 12
    if full == 1:
        assert correction <= 2 and not q211
    if full == 2:
        assert B == 12 and correction == 0 and not q211
    return direct, B, full, correction, q211

records = []
expected = (0, 0, 2, 9, 11, 18)
for d in range(6):
    hist = Counter()
    cases = Counter()
    best = None
    for indices in combinations(range(27), d):
        if time.monotonic() - START > DEADLINE:
            raise TimeoutError('No complete-domain claim: sixty-second deadline exceeded')
        D = sum(1 << i for i in indices)
        weight, B, full, correction, q = evaluate(D)
        hist[weight] += 1
        cases[(full, bool(q))] += 1
        if best is None or weight > best['weight']:
            best = dict(weight=weight, omitted_indices=indices,
                        omitted_sets=[points(A[i]) for i in indices],
                        B=B, full_rows=full, correction=correction, q211=q)
    assert sum(hist.values()) == math.comb(27, d)
    assert max(hist) == expected[d]
    records.append(dict(d=d, checked=math.comb(27, d), maximum=max(hist),
                        bound_under_H27=54-d+max(hist), witness=best,
                        histogram=dict(sorted(hist.items())),
                        structural_case_counts={str(k): v for k, v in sorted(cases.items())}))
result = dict(evidence_grade='certificate-diagnostic',
              theorem_status='ordinary proof in STABILITY.md; no Lean claim',
              source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              domain=dict(AHS_blocks=27, nonmember_nonempty_traces=228,
                          omission_subsets_checked=sum(r['checked'] for r in records),
                          exterior_support='arbitrary; handled by trace-fibre argument'),
              local_blocker_certificates=local, deletion_table=records,
              runtime_seconds=time.monotonic()-START)
(HERE / 'stability_certificate.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k != 'local_blocker_certificates'}, indent=2))
