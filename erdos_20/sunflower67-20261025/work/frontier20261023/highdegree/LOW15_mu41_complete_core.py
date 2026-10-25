#!/usr/bin/env python3
"""Prepared necessary complete-core systems for mu41, cap15, and NO9.

Standard library only; no solver. Importing this module does not enumerate
rows or cores. The explicit commands below are work commands, not tests.
No command was executed when this source was prepared.

Unlike the prior LOW15 primary, this does not import mu42, r9=r10=7,
minimum degree4, or a cap on the ambient exterior support. A node limit
raises IncompleteCensus: it never certifies an exhausted branch.
"""
from functools import lru_cache
from itertools import combinations, permutations
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json

HERE = Path(__file__).resolve().parent
WORK = HERE.parents[1]
LOCAL43 = (WORK / "frontier20261020/prior-art68/repository/companion/upstream/"
           "LOW15/scripts/inputs/local43.py")
LOCAL43_SHA256 = "258221ffe8594e51616bdd125109d92151bfea13557f4e385ef453ab2e03152b"
NOTE_HASHES = {
    "LOW15-NO9-fibre-route.md": "576a463ffc3c86138e53d6919f75ead7274a6dd46401a69bc3b6ca8e3b41e0b1",
    "LOW15-two-low-core.md": "6f09a59a3705b93c38f21a6a5eb3de725540d321876ed620bb56f95fd7130bb1",
    "LOW15-large-singleton-core.md": "164460b2b3c60fe6bcf6ea36164350ef949efc253d74e3236f08fd6d6225d482",
}
PAIRS = tuple(combinations(range(4), 2))
PERMS = tuple(permutations(range(4)))
ROOT = frozenset(range(4))
ROOT_MASK = 15
CODEGREE_CAP = {1: 15, 2: 6, 3: 2, 4: 1}
N44_REMAINING = (
    (1, 3, 3, 3, 3, 0),
    (2, 2, 3, 3, 2, 1),
    (3, 1, 3, 3, 1, 2),
    (3, 2, 2, 2, 2, 2),
)


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def dependencies():
    out = []
    for path, expected in [(LOCAL43, LOCAL43_SHA256)] + [
            (HERE / name, digest) for name, digest in NOTE_HASHES.items()]:
        actual = sha256(path)
        if actual != expected:
            raise ValueError(f"Dependency changed: {path}")
        out.append({"path": str(path), "sha256": actual})
    return out


@lru_cache(None)
def local43():
    dependencies()
    spec = importlib.util.spec_from_file_location("low15_mu41_local43", LOCAL43)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def degree(row):
    total_triples = sum(row[6:10])
    return tuple(1 + row[10+i] + total_triples - row[6+i]
                 + sum(row[j] for j, pair in enumerate(PAIRS) if i in pair)
                 for i in range(4))


def relabel_row(row, perm):
    """New position i denotes old point perm[i]; omitted triples move too."""
    return (tuple(row[PAIRS.index(tuple(sorted((perm[i], perm[j]))))]
                  for i, j in PAIRS)
            + tuple(row[6+perm[i]] for i in range(4))
            + tuple(row[10+perm[i]] for i in range(4)))


@lru_cache(None)
def rows():
    """Necessary local rows, initially ordered by nondecreasing degree."""
    return tuple(sorted(tuple(row) for row in local43().enumerate_rows(
        mu=41, r10=0, r9=0, cap_degree=15)
        if max(row[10:14]) <= 8 and 1 + sum(row) <= 44))


@lru_cache(None)
def oriented_rows():
    return tuple(sorted({relabel_row(row, perm)
                         for row in rows() for perm in PERMS}))


def high_rows(neighbourhood):
    """S4 representatives only; no geometric or LP exclusion asserted."""
    if neighbourhood not in (43, 44):
        raise ValueError("This high-core interface is for N43 or N44")
    return tuple(sorted({min(relabel_row(row, perm) for perm in PERMS)
                         for row in rows() if 1 + sum(row) == neighbourhood}))


def mask(points):
    return sum(1 << v for v in points)


def sunflower(a, b, c):
    return a & b == a & c == b & c


class IncompleteCensus(RuntimeError):
    pass


def category_extensions(used, local_size, edges, root):
    """Every old/fresh identification, modulo fresh-label first appearance.

    Exterior labels are 4,5,... . New vertices within one category are
    distinct, but vertices in different categories may be identified.
    """
    seen = set()
    for fresh in range(local_size + 1):
        fresh_labels = set(range(used, used + fresh))
        for embedding in permutations(range(used + fresh), local_size):
            if not fresh_labels <= set(embedding):
                continue
            appeared = [x for x in embedding if x >= used]
            if appeared != sorted(appeared):
                continue
            extra = tuple(sorted(tuple(sorted(root | {4+embedding[v] for v in edge}))
                                 for edge in edges))
            if extra not in seen:
                seen.add(extra)
                yield tuple(map(frozenset, extra)), used + fresh


def generate_cores(row, stats=None, max_nodes=None):
    """Generate every complete prescribed root core, possibly isomorphic twice.

    The fresh-label construction is exhaustive without an a priori support
    cutoff. Exact duplicates are removed, but no factorial canonical-label
    search is needed for correctness. A finite diagnostic limit is a failure
    to finish, never a mathematical exclusion.
    """
    row = tuple(row)
    if row not in oriented_rows():
        raise ValueError("Root row is outside the pinned necessary domain")
    if 1 + sum(row) not in (43, 44):
        raise ValueError("Expected an N43 or N44 high root")
    big = {i for i, s in enumerate(row[10:14]) if s == 8}
    cats = []
    edge_shapes = {1: ((0, 1),), 2: ((0, 1), (0, 2)),
                   3: ((0, 1), (0, 2), (1, 2))}
    for j, count in enumerate(row[:6]):
        if count:
            cats.append((2 if count == 1 else 3, edge_shapes[count],
                         frozenset(PAIRS[j]), ("pair", j)))
    for j, count in enumerate(row[6:10]):
        if count:
            cats.append((1, ((0,),), ROOT - {j}, ("triple", j)))
    cats.sort(key=lambda cat: (-len(cat[1]), -len(cat[2] & big),
                              -len(cat[2]), cat[3]))
    if stats is None:
        stats = {}
    stats.update(nodes=0, leaves=0, unique_labelled_cores=0, exhausted=False)
    seen = set()

    def visit(at, used, family):
        stats["nodes"] += 1
        if max_nodes is not None and stats["nodes"] > max_nodes:
            raise IncompleteCensus(f"Node limit {max_nodes} reached; census incomplete")
        if at == len(cats):
            stats["leaves"] += 1
            key = tuple(sorted(tuple(sorted(q)) for q in family))
            if key not in seen:
                seen.add(key)
                stats["unique_labelled_cores"] += 1
                yield key
            return
        size, edges, root, _ = cats[at]
        for extra, next_used in category_extensions(used, size, edges, root):
            augmented = list(family)
            for block in extra:
                if block in augmented:
                    break
                # Both blocks are near at this known singleton8 root.
                if any(len(block & q) == 1 and block & q <= big for q in augmented):
                    break
                if any(sunflower(block, q, q2) for q, q2 in combinations(augmented, 2)):
                    break
                augmented.append(block)
            else:
                yield from visit(at + 1, next_used, tuple(augmented))

    yield from visit(0, 0, (ROOT,))
    stats["exhausted"] = True


def validate_core(core, row):
    core = tuple(tuple(sorted(q)) for q in core)
    if not core or len(set(core)) != len(core):
        raise ValueError("Core must be a nonempty simple family")
    if any(len(q) != 4 or len(set(q)) != 4 or min(q) < 0 for q in core):
        raise ValueError("Every core member must be a four-set of nonnegative labels")
    support = set().union(*map(set, core))
    if support != set(range(max(support) + 1)) or tuple(range(4)) not in core:
        raise ValueError("Expected normalized support and actual root 0123")
    fixed = tuple(mask(q) for q in core)
    if any((q & ROOT_MASK).bit_count() < 2 for q in fixed):
        raise ValueError("This interface requires the COMPLETE >=2 root core")
    expected = tuple(sum((q & ROOT_MASK) == mask(pair) for q in fixed) for pair in PAIRS)
    expected += tuple(sum((q & ROOT_MASK) == (ROOT_MASK ^ (1 << i)) for q in fixed)
                      for i in range(4))
    if expected != tuple(row[:10]):
        raise ValueError("Core does not have the prescribed pair/triple categories")
    if len(core) != 1 + sum(row[:10]) or any(sunflower(*abc) for abc in combinations(fixed, 3)):
        raise ValueError("Core cardinality or sunflower condition failed")
    for size in (1, 2, 3):
        for points in combinations(range(len(support)), size):
            subset = mask(points)
            if sum(q & subset == subset for q in fixed) > CODEGREE_CAP[size]:
                raise ValueError("Core exceeds an imported global codegree cap")
    return tuple(sorted(core))


def trace_data(core):
    fixed = tuple(mask(q) for q in core)
    n = 1 + max(max(q) for q in core)
    fixed_pairs = tuple((a, b, a & b) for a, b in combinations(fixed, 2))
    candidates, caps = [], []
    for size in range(5):
        for points in combinations(range(n), size):
            trace = mask(points)
            if (trace & ROOT_MASK).bit_count() >= 2:
                continue
            if any(a & trace == common and b & trace == common
                   for a, b, common in fixed_pairs):
                continue
            # The empty-trace pool is inside the intersecting disjoint
            # complement of R. Nonempty traces use global codegree caps.
            upper = (27 if size == 0 else CODEGREE_CAP[size]
                     - sum(q & trace == trace for q in fixed))
            if upper > 0:
                candidates.append(trace)
                caps.append(upper)
    return fixed, n, tuple(candidates), tuple(caps)


def anchor_domain(core, given_row, anchor, data):
    fixed, _, candidates, caps = data
    anchor = tuple(anchor)
    am = mask(anchor)
    features = (tuple(mask((anchor[i], anchor[j])) for i, j in PAIRS)
                + tuple(am ^ (1 << v) for v in anchor)
                + tuple(1 << v for v in anchor))
    lows = tuple(sum(q & am == trace for q in fixed) for trace in features)
    uppers = tuple(lo + sum(cap for trace, cap in zip(candidates, caps) if trace & am == feature)
                   for lo, feature in zip(lows, features))
    prescribed_degrees = degree(given_row)
    fixed_degrees = {v: sum(bool(q & (1 << v)) for q in fixed) for v in anchor}
    # Known disjoint near triples forbid a singleton8 choice at this
    # actual anchor, by B4. This filter uses literal fixed members only.
    forbid_eight = set()
    for i, v in enumerate(anchor):
        near = [q for q in fixed if q & (1 << v) and (q & am).bit_count() >= 2]
        if any(a & b == 1 << v for a, b in combinations(near, 2)):
            forbid_eight.add(i)
    live = []
    for row in oriented_rows():
        if am == ROOT_MASK and row != tuple(given_row):
            continue
        degrees = degree(row)
        if any(degrees[i] != prescribed_degrees[v] for i, v in enumerate(anchor) if v < 4):
            continue
        if any(degrees[i] < fixed_degrees[v] for i, v in enumerate(anchor)):
            continue
        if any(row[10+i] == 8 for i in forbid_eight):
            continue
        if any(value < lo or value > hi for value, lo, hi in zip(row, lows, uppers)):
            continue
        live.append(row)
    return features, lows, tuple(live)


def build(core, given_row):
    """Return a necessary integer-coefficient LP; no solver is called.

    Actual families select one local row per actual fixed anchor and assign
    integer trace multiplicities. The emitted [0,1] selectors and trace
    boxes relax those integral assignments. Empty live domains are emitted
    as 0=1, so a caller can retain a directly checkable contradiction.
    """
    before = dependencies()
    given_row = tuple(given_row)
    if given_row not in oriented_rows():
        raise ValueError("Root row is outside the necessary domain")
    core = validate_core(core, given_row)
    data = trace_data(core)
    fixed, n, candidates, caps = data
    bounds = [(0, cap) for cap in caps]
    names = [["trace", [v for v in range(n) if trace & (1 << v)]] for trace in candidates]
    equal = [("family-size68", {i: 1 for i in range(len(candidates))}, 68-len(core))]
    upper, live_sizes = [], []
    for anchor in core:
        features, lows, live = anchor_domain(core, given_row, anchor, data)
        am = mask(anchor)
        offset = len(bounds)
        bounds.extend([(0, 1)] * len(live))
        names.extend([["local-row", list(anchor), list(row)] for row in live])
        live_sizes.append(len(live))
        equal.append((f"choose:{anchor}", {offset+j: 1 for j in range(len(live))}, 1))
        for i, feature in enumerate(features):
            coefficients = {j: 1 for j, trace in enumerate(candidates) if trace & am == feature}
            coefficients.update({offset+j: -row[i] for j, row in enumerate(live) if row[i]})
            equal.append((f"trace:{anchor}:{feature}", coefficients, -lows[i]))
    for size in (1, 2, 3):
        for points in combinations(range(n), size):
            subset = mask(points)
            coefficients = {j: 1 for j, trace in enumerate(candidates) if trace & subset == subset}
            rhs = CODEGREE_CAP[size] - sum(q & subset == subset for q in fixed)
            upper.append((f"global-cap:{points}", coefficients, rhs))
    # This is redundant with family mass and the root feature equations,
    # but it records precisely how the arbitrary exterior pool is counted.
    equal.append(("disjoint-root-cardinality", {
        j: 1 for j, trace in enumerate(candidates) if trace & ROOT_MASK == 0},
        68 - (1 + sum(given_row))))
    after = dependencies()
    if after != before:
        raise ValueError("Dependencies changed during model construction")
    return {"schema": "low15-mu41-complete-root-core-v1",
            "status": "NECESSARY_RELAXATION_BUILT_NOT_SOLVED",
            "source_sha256": sha256(__file__), "dependencies": before,
            "premises": {"family_cardinality": 68, "mu": 41, "maximum_neighbourhood": 44,
                         "maximum_point_degree": 15, "maximum_exact_singleton": 8,
                         "r9_bootstrap": 0, "r10_bootstrap": 0,
                         "complete_root_core": True, "arbitrary_exterior_multiplicity": True,
                         "imports": ["H27", "B4", "I8/I9/I10 and isolation",
                                     "universal local43 foundations", "cap15 NO45 then NO9"]},
            "row": list(given_row), "core": [list(q) for q in core],
            "represented_points": list(range(n)), "root_degrees": list(degree(given_row)),
            "candidates": list(candidates), "bounds": bounds, "equal": equal,
            "upper": upper, "variable_names": names, "live_sizes": live_sizes}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    pr = sub.add_parser("rows")
    pr.add_argument("--N", type=int, choices=(43, 44), required=True)
    pr.add_argument("--output", type=Path, required=True)
    pc = sub.add_parser("cores")
    pc.add_argument("--row", required=True, help="JSON array p[6]+t[4]+s[4]")
    pc.add_argument("--max-nodes", type=int, required=True)
    pc.add_argument("--output", type=Path, required=True)
    pm = sub.add_parser("model")
    pm.add_argument("--input", type=Path, required=True, help="JSON with exact core and row")
    pm.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "rows":
        result = {"source_sha256": sha256(__file__), "dependencies": dependencies(),
                  "N": args.N, "rows": high_rows(args.N),
                  "status": "NECESSARY_ARITHMETIC_DOMAIN_ONLY"}
    elif args.command == "cores":
        row = tuple(json.loads(args.row))
        stats = {}
        cores = list(generate_cores(row, stats, args.max_nodes))
        result = {"source_sha256": sha256(__file__), "dependencies": dependencies(),
                  "row": row, "cores": cores, "stats": stats,
                  "status": "ROOT_CORES_EXHAUSTED_NOT_EXTENSION_TESTED"}
    else:
        source = json.loads(args.input.read_text())
        result = build(source["core"], source["row"])
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"output": str(args.output), "status": result["status"]}))


if __name__ == "__main__":
    main()
