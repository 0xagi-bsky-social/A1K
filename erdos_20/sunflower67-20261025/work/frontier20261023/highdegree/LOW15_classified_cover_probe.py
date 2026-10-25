#!/usr/bin/env python3
"""Bounded discovery census, never an LP or independent I7 classification.

The classified-model and arbitrary-support premises are recorded in the JSON.
Every ambient four-cover has >=3 support points after <=2 deletions.  The raw
bound is twice the number of support three-covers plus the number of support
four-covers containing no such triple.  Optional reductions below are literal
global pair/triple-incidence inequalities, not presumed simultaneous choices.
"""
import argparse
import hashlib
import itertools as it
import json
import time
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
PAPER = HERE.parents[1] / "frontier20261020/prior-art68/repository/paper/main.tex"
I7 = [
    "012 034 134 035 235 145 245",
    "012 034 234 135 235 145 245",
    "012 134 234 135 235 145 245",
    "013 024 134 125 235 045 345",
    "023 124 134 125 235 045 345",
    "014 234 025 125 035 145 345",
    "134 234 125 035 135 045 245",
    "023 024 034 124 134 015 016",
]
P10 = "012 015 023 034 045 124 134 135 235 245"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def triples(s):
    return tuple(frozenset(map(int, t)) for t in s.split())


def encode(s):
    return sum(1 << v for v in s)


def points(mask):
    return [v for v in range(mask.bit_length()) if mask >> v & 1]


def sf3(L):
    return not any((a & b) == (a & c) == (b & c)
                   for a, b, c in it.combinations(L, 3))


def normalized_models():
    """No isomorphism quotient is needed to cover every permitted gluing."""
    d, e = (4, 5, 6), (7, 8, 9)
    r16 = [frozenset((h,) + p) for h in (0, 1)
           for p in it.combinations(d, 2)]
    r16 += list(map(frozenset, it.combinations((0, 1, 2, 3), 3)))
    r16 += [frozenset((h,) + p) for h in (2, 3)
            for p in it.combinations(e, 2)]
    for omitted in range(16):
        yield f"R15-delete-{omitted:02d}", tuple(r16[:omitted] + r16[omitted+1:]), {
            "kind": "R15", "omitted_R16_triple": sorted(r16[omitted])}

    for kind, removed in (("P8-i1", ("034", "135")),
                          ("P8-i2", ("012", "015"))):
        h = tuple(t for t in triples(P10) if t not in triples(" ".join(removed)))
        for j, text in enumerate(I7):
            k = tuple(frozenset(v + 6 for v in t) for t in triples(text))
            yield f"{kind}-H{j}", h + k, {"kind": kind, "I7": j}

    # Q8 core is 0..4; every K point is outside that core.  Its two
    # distinct leaves can both be fresh, one can be a K point, or both
    # can be distinct K points.  The leaf swap removes their ordering.
    core = tuple(frozenset((h,) + p) for h in (0, 1)
                 for p in it.combinations((2, 3, 4), 2))
    for j, text in enumerate(I7):
        k = tuple(frozenset(v + 5 for v in t) for t in triples(text))
        w = sorted(set().union(*k))
        fresh = max(w) + 1
        leaves = [(fresh, fresh + 1)] + [(v, fresh) for v in w]
        leaves += list(it.combinations(w, 2))
        for index, pair in enumerate(leaves):
            h = core + tuple(frozenset((0, 1, v)) for v in pair)
            yield f"Q8-H{j}-glue-{index:02d}", h + k, {
                "kind": "Q8", "I7": j, "leaves": list(pair),
                "K_support": w}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, default=HERE / "LOW15-classified-cover-probe.json")
    ap.add_argument("--seconds", type=float, default=10.0)
    args = ap.parse_args()
    if not 0 < args.seconds <= 10:
        raise SystemExit("deadline must be positive and at most10 seconds")
    started = time.monotonic()
    source_sha = digest(Path(__file__))
    deadline = started + args.seconds
    def tick():
        if time.monotonic() > deadline:
            raise TimeoutError("bounded discovery deadline exceeded")

    results, rejected, all_cases = [], [], []
    hist = {d: Counter() for d in range(3)}
    raw_hist = {d: Counter() for d in range(3)}
    exceptions = []
    for name, raw_L, metadata in normalized_models():
        tick()
        L = tuple(sorted(encode(t) for t in raw_L))
        if len(L) != 15 or len(set(L)) != 15:
            raise RuntimeError("malformed link " + name)
        if not sf3(L):
            rejected.append({"model": name, "reason": "literal SF3 violation"})
            continue
        W = sorted(set().union(*raw_L))
        degrees = {v: sum(bool(T >> v & 1) for T in L) for v in W}
        if max(degrees.values()) > 6:
            raise RuntimeError("SF3 point-degree premise failed " + name)
        D = [sum(1 << i for i in indices) for d in range(3)
             for indices in it.combinations(range(15), d)]
        c3 = {mask: [] for mask in D}
        c4 = {mask: [] for mask in D}
        for size, target in ((3, c3), (4, c4)):
            for choice in it.combinations(W, size):
                S = encode(choice)
                missing = sum(1 << i for i, T in enumerate(L) if not S & T)
                missing_count = missing.bit_count()
                if missing_count > 2:
                    continue
                remaining = [i for i in range(15) if not missing >> i & 1]
                for extra_count in range(3 - missing_count):
                    for extra in it.combinations(remaining, extra_count):
                        deletion = missing | sum(1 << i for i in extra)
                        target[deletion].append(S)
        per_d = {d: {"raw_max": 0, "safe_max": 0, "cases": 0} for d in range(3)}
        for deletion in D:
            tick()
            d = deletion.bit_count()
            triples3 = c3[deletion]
            pure4 = [Q for Q in c4[deletion]
                     if not any(T & Q == T for T in triples3)]
            raw = 2 * len(triples3) + len(pure4)
            bound = raw
            reduction = None
            generators = triples3 + pure4
            if generators:
                common = generators[0]
                for S in generators[1:]:
                    common &= S
                for pair in it.combinations(points(common), 2):
                    P = encode(pair)
                    cone_occupancy = sum(T & P == P for T in L)
                    cap = 6 - cone_occupancy
                    if cap < bound:
                        bound = cap
                        reduction = {"type": "common_pair", "pair": list(pair),
                                     "prescribed_cones": cone_occupancy, "bound": cap}
                if not triples3:
                    union = 0
                    for Q in pure4:
                        union |= Q
                    for z in points(common):
                        remaining_support = points(union & ~(1 << z))
                        # Every residual triple uses3 pairs; each ambient
                        # triple z+a+b has capacity2, reduced by its actual
                        # prescribed x-cone if that triple belongs to L.
                        budget = sum(2 - int(encode((z,) + p) in L)
                                     for p in it.combinations(remaining_support, 2))
                        cap = budget // 3
                        if cap < bound:
                            bound = cap
                            reduction = {"type": "common_point_pair_budget", "point": z,
                                         "residual_support": remaining_support,
                                         "budget": budget, "bound": cap}
            hist[d][bound] += 1
            raw_hist[d][raw] += 1
            per_d[d]["raw_max"] = max(per_d[d]["raw_max"], raw)
            per_d[d]["safe_max"] = max(per_d[d]["safe_max"], bound)
            per_d[d]["cases"] += 1
            row = {"model": name, "deletion": deletion, "d": d,
                   "C3": triples3, "P4": pure4, "raw": raw, "safe": bound,
                   "reduction": reduction}
            all_cases.append(row)
            target = 8 if d == 0 and metadata["kind"] == "R15" else (4, 10, 11)[d]
            if bound > target:
                exceptions.append(row)
        results.append({"model": name, **metadata,
                        "link": [points(T) for T in L], "support": W,
                        "point_degrees": degrees, "bounds": per_d})
    elapsed = time.monotonic() - started
    payload = {
        "status": "discovery census completed; conditional upper bounds only",
        "source_sha256": source_sha, "paper_sha256": digest(PAPER),
        "premises": [
            "Simple SF4 family, global pair codegree<=6 and triple codegree<=2.",
            "The displayed15 triples are the complete link of an actual point x.",
            "rho7 classification supplies R16 minus one; no rho<=6 classification asserted.",
            "8+7 split uses B4 and P8/Q8 isolation; every opposite I7 is one of the imported eight templates.",
            "P8 support avoids opposite support; Q8 five-point core avoids opposite support, leaves may overlap.",
            "After<=2 deletions at least13 triples remain; maxlinkdegree6 implies every ambient cover has>=3 support points.",
            "C3 exterior completions use global triple capacity2; pure internal P4 candidates use simplicity.",
            "No finite diagnostic is a Lean theorem or an independent replay of the imported I7 catalogue."
        ],
        "models": results, "rejected_gluings": rejected,
        "model_count": len(results), "case_count": len(all_cases),
        "safe_histograms": hist, "raw_histograms": raw_hist,
        "case_relation_sha256": hashlib.sha256(json.dumps(all_cases, sort_keys=True,
            separators=(",", ":")).encode()).hexdigest(),
        "unclosed_cases": exceptions, "unclosed_count": len(exceptions),
        "seconds": elapsed,
    }
    if digest(Path(__file__)) != source_sha:
        raise RuntimeError("source changed during discovery census")
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"output": str(args.output), "models": len(results),
        "cases": len(all_cases), "unclosed": len(exceptions),
        "safe_max": {d: max(hist[d], default=0) for d in hist},
        "raw_max": {d: max(raw_hist[d], default=0) for d in raw_hist},
        "seconds": elapsed, "source_sha256": source_sha}, sort_keys=True))


if __name__ == "__main__":
    main()
