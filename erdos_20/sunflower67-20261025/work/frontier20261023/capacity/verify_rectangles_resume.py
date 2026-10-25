"""Exact factorized pair/triple check, independent of the gluing proof.

Reads the literal witness and rectangle data, imports no project checker.
It checks all triples of rectangles with repetition and all realizable
block equality patterns. This is research validation, not Lean verification.
"""
from pathlib import Path
from itertools import combinations, combinations_with_replacement, product
from hashlib import sha256
import json, math, random, time

P = Path(__file__).resolve().parent
t0 = time.monotonic()

def diff(a, b, c):
    return int(a != b) | (int(a != c) << 1) | (int(b != c) << 2)

def relations(sides):
    pair = {}
    tri = {}
    for i, j in product(range(len(sides)), repeat=2):
        pair[i, j] = {int(x != y) for x in sides[i] for y in sides[j] if x & y == x}
    for i, j, k in product(range(len(sides)), repeat=3):
        tri[i, j, k] = {diff(x, y, z) for x in sides[i] for y in sides[j] for z in sides[k]
                        if x & y == x & z == y & z}
    return pair, tri

def check(rectangles, sides):
    pair, tri = relations(sides)
    badpair = None
    badtriple = None
    # Include identical rectangles: different points of one rectangle can
    # still be distinct sets, so the strictness flags must also be tested.
    for r, s in product(rectangles, repeat=2):
        if r[0] & s[0] == r[0] and pair[r[1], s[1]] and pair[r[2], s[2]]:
            if r[0] != s[0] or 1 in pair[r[1], s[1]] or 1 in pair[r[2], s[2]]:
                badpair = [r, s]
                break
    for r, s, t in combinations_with_replacement(rectangles, 3):
        if r[0] & s[0] != r[0] & t[0] or r[0] & s[0] != s[0] & t[0]:
            continue
        d = diff(r[0], s[0], t[0])
        if any(d | x | y == 7 for x in tri[r[1], s[1], t[1]]
               for y in tri[r[2], s[2], t[2]]):
            badtriple = [r, s, t]
            break
    return badpair is not None, badtriple is not None

def materialize(rectangles, sides, width):
    return {r[0] | (x << width) | (y << (2 * width))
            for r in rectangles for x in sides[r[1]] for y in sides[r[2]]}

def brute(S):
    return (any(a & b in (a, b) for a, b in combinations(S, 2)),
            any(a & b == a & c == b & c for a, b, c in combinations(S, 3)))

# Test factorization against literal exhaustive enumeration on small,
# seeded cases, including arbitrary overlap and repeated rectangle labels.
rng = random.Random(20261023)
controls = []
for _ in range(180):
    small_sides = [sorted(rng.sample(range(4), rng.randrange(1, 5))) for _ in range(3)]
    rr = [tuple([rng.randrange(4), rng.randrange(3), rng.randrange(3)])
          for _ in range(rng.randrange(1, 7))]
    actual = check(rr, small_sides)
    expected = brute(materialize(rr, small_sides, 2))
    if actual != expected:
        raise RuntimeError((rr, small_sides, actual, expected))
    controls.append(expected)
assert any(x[0] for x in controls) and any(x[1] for x in controls)

# Reconstruct H directly from its three orbit representatives.
H = {sum(1 << ((a * x + b) % 11) for x in S)
     for S in [(0, 1, 2, 3, 4, 5, 6), (0, 1, 2, 3, 4, 6, 7), (0, 1, 2, 6, 9)]
     for a in [1, 3, 4, 5, 9] for b in range(11)}
sides = [[h >> 1 for h in sorted(H) if h & 1 == v] for v in [0, 1]] + [[0]]
data = json.loads((P / 'candidate28.rectangles.json').read_text())
assert data['points'] == 28 and data['block_sizes'] == [8, 10, 10]
rr = [tuple(r[:3]) for r in data['rectangles']]
assert len(rr) == 105 and len(set(rr)) == 105
literal = [int(s) for s in (P / 'candidate28.masks').read_text().splitlines()]
rebuilt = {r[0] | (x << 8) | (y << 18) for r in rr for x in sides[r[1]] for y in sides[r[2]]}
assert len(literal) == len(set(literal)) == len(rebuilt) == 252271
assert set(literal) == rebuilt
assert sum(len(sides[r[1]]) * len(sides[r[2]]) for r in rr) == len(rebuilt)
assert all(0 <= r[0] < 256 for r in rr)
assert len(H) == 121 and [len(s) for s in sides] == [46, 75, 1]
assert check(rr, sides) == (False, False)
# Three nonempty singleton core masks with empty branch parts are a
# planted empty-core sunflower, checked inside the entire candidate domain.
planted = rr + [(1, 2, 2), (2, 2, 2), (4, 2, 2)]
assert check(planted, sides)[1]
assert check(rr + [(0, 2, 2)], sides)[0]
N = [sum((s & 1) * 2 + ((s >> 1) & 1) == k for s in literal) for k in range(4)]
assert N == [33948, 64728, 64728, 88867]
record = {
    'result': 'PASS', 'method': 'factorized exhaustive pair/triple checker; no project imports',
    'rectangles': len(rr), 'ordered_rectangle_pairs': len(rr) ** 2,
    'unordered_rectangle_triples_with_repetition': math.comb(len(rr) + 2, 3),
    'block_state_triples': 27, 'literal_members': len(literal), 'port_counts': N,
    'random_small_cases_cross_checked_by_brute_force': len(controls),
    'full_domain_planted_sunflower_rejected': True, 'full_domain_empty_set_containment_rejected': True,
    'witness_sha256': sha256((P / 'candidate28.masks').read_bytes()).hexdigest(),
    'checker_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
    'seconds': time.monotonic() - t0,
    'assurance': 'certificate-diagnostic; separate algorithm in the same AI workflow; no Lean kernel check or independent third-party reproduction',
}
(P / 'verify_rectangles_resume.result.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
