#!/usr/bin/env python3
"""Small exact cap15 arithmetic census. No LP or geometric realization claim.

The variables are exact traces of one actual four-member anchor. All S4
actions move p, t (indexed by omitted point), and s together. This is a
complete arithmetic superset, never a classification of exterior supports.
"""
from collections import Counter, defaultdict
from itertools import combinations, combinations_with_replacement, permutations, product
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PAIRS = tuple(combinations(range(4), 2))
PAIR_INDEX = {p: i for i, p in enumerate(PAIRS)}
PERMS = tuple(permutations(range(4)))


def act(row, perm):
    p, t, s = row[:6], row[6:10], row[10:14]
    pp, tt, ss = [0]*6, [0]*4, [0]*4
    for n, (i, j) in enumerate(PAIRS):
        pp[PAIR_INDEX[tuple(sorted((perm[i], perm[j])))]] = p[n]
    for i in range(4):
        tt[perm[i]], ss[perm[i]] = t[i], s[i]
    return tuple(pp + tt + ss)


def features(row):
    p, t, s = row[:6], row[6:10], row[10:14]
    T = sum(t)
    r = [sum(p[n] for n, e in enumerate(PAIRS) if i in e) for i in range(4)]
    k = [1 + r[i] + T - t[i] for i in range(4)]
    d = [s[i]+k[i] for i in range(4)]
    return p, t, s, r, k, d


def b4_rejections(row):
    p, t, s, r, _, _ = features(row)
    reasons = []
    # If t_l=1, every pair-category lj at a B4 point j must use the
    # external point of that triple. Three distinct intersecting SF2
    # edges cannot all contain one point, so p_lj<=2.
    for n, (i, j) in enumerate(PAIRS):
        if p[n] == 3 and ((t[i] and s[j] >= 8) or (t[j] and s[i] >= 8)):
            reasons.append("triple-point-cannot-cover-pair-triangle")
    # If all three j != l are B4 points, the entire row l at that
    # external point is a bipartite graph of maxdegree2 and matching<=2.
    # Hence it has at most4 edges. No exterior support bound is used.
    for l in range(4):
        if t[l] and all(s[j] >= 8 for j in range(4) if j != l) and r[l] > 4:
            reasons.append("triple-star-bipartite-edge-cap4")
    return sorted(set(reasons))


def triangle_propagation(row):
    """A sufficient ordinary triangle-support propagation rule, not a census.

    B4 vertices of pair-row at least5 have a unique exterior triangle.
    A shared category of size2 or3 identifies those triangles. At a
    (3,1,1) vertex its two singleton edges are distinct, so if their
    other endpoints have already identified triangles, these identify
    its triangle as well.
    """
    p, t, s, r, _, _ = features(row)
    good = {i for i in range(4) if s[i] >= 8 and r[i] >= 5}
    parent = list(range(4))
    def root(i):
        while parent[i] != i:
            i = parent[i]
        return i
    def join(i, j):
        a, b = root(i), root(j)
        if a == b:
            return False
        parent[b] = a
        return True
    for n, (i, j) in enumerate(PAIRS):
        if p[n] >= 2 and i in good and j in good:
            join(i, j)
    changed = True
    while changed:
        changed = False
        for i in good:
            incident = [(j, p[PAIR_INDEX[tuple(sorted((i, j)))]])
                        for j in range(4) if j != i]
            if sorted(v for _, v in incident) != [1, 1, 3]:
                continue
            j, k = [j for j, v in incident if v == 1]
            if j in good and k in good and root(j) == root(k):
                changed |= join(i, j)
    covered = all(v == 0 or i in good or j in good
                  for v, (i, j) in zip(p, PAIRS))
    unified = bool(good) and len({root(i) for i in good}) == 1
    forced_common = covered and unified
    return {"B4_triangle_vertices": sorted(good),
            "all_pair_categories_forced_on_one_triangle": forced_common,
            "triangle_row_capacity_contradiction": forced_common and max(r) > 6}


def complete_P9_complement_guard(row):
    p, t, s, _, _, _ = features(row)
    witnesses = []
    for l in range(4):
        if not (t[l] == 1 and s[l] == 9):
            continue
        for j in range(4):
            if j != l and s[j] >= 8 and p[PAIR_INDEX[tuple(sorted((l, j)))]] > 0:
                witnesses.append([l, j])
    return witnesses


def triple_triangle_point_overload(row):
    p, t, s, r, _, _ = features(row)
    witnesses = []
    for l in range(4):
        if not (t[l] and s[l] >= 8 and r[l] >= 5):
            continue
        entries = [(j, p[PAIR_INDEX[tuple(sorted((l, j)))]])
                   for j in range(4) if j != l]
        if not any(s[j] >= 8 and v for j, v in entries):
            continue
        lower = sum(v if s[j] >= 8 else max(v-1, 0) for j, v in entries)
        if lower > 4:
            witnesses.append({"omitted_point": l, "forced_triangle_point_occurrences": lower,
                              "capacity": 4})
    return witnesses


def census():
    possible_s = [s for s in combinations_with_replacement(range(10), 4)
                  if sum(s) >= 32 and sum(s[1:]) <= 26]
    p_by_total = defaultdict(list)
    for p in product(range(4), repeat=6):
        if 8 <= sum(p) <= 12:
            p_by_total[sum(p)].append(p)
    canonical = {}
    for s in possible_s:
        for t in product(range(2), repeat=4):
            for N in (45, 46):
                P = N - 1 - sum(s) - sum(t)
                if 2*N + 2 - sum(s) + sum(t) > 60:
                    continue
                for p in p_by_total.get(P, ()):
                    row = p + t + s
                    _, _, _, r, k, d = features(row)
                    if max(d) > 15:
                        continue
                    # Global pair-codegree cap at an actual anchor.
                    if any(1 + p[n] + sum(t[h] for h in range(4) if h not in e) > 6
                           for n, e in enumerate(PAIRS)):
                        continue
                    assert sum(d) == 2*N+2-sum(s)+sum(t)
                    assert sum(k) == 4+2*P+3*sum(t)
                    orbit = {act(row, perm) for perm in PERMS}
                    rep = min(orbit)
                    if rep in canonical:
                        continue
                    pp, tt, ss, rr, kk, dd = features(rep)
                    reasons = b4_rejections(rep)
                    canonical[rep] = {
                        "N": N, "p": list(pp), "t": list(tt), "s": list(ss),
                        "pair_rows": rr, "near": kk, "degrees": dd,
                        "sorted_singletons": sorted(ss), "orbit_size": len(orbit),
                        "b4_rejections": reasons,
                        "passes_b4_arithmetic": not reasons,
                        "common_triangle_terminal_guard":
                            min(ss) >= 8 and sum(tt) == 0 and min(rr) >= 5,
                        "triangle_propagation": triangle_propagation(rep),
                        "complete_P9_complement_guard_witnesses":
                            complete_P9_complement_guard(rep),
                        "triple_triangle_point_overload": triple_triangle_point_overload(rep),
                    }
    records = []
    for i, (_, rec) in enumerate(sorted(canonical.items())):
        rec["id"] = f"CAP15_HIGH_{i:03d}"
        records.append(rec)
    summaries = {}
    for N in (45, 46):
        nr = [r for r in records if r["N"] == N]
        surviving = [r for r in nr if r["passes_b4_arithmetic"]]
        def counts(rs):
            return {"orbits": len(rs), "oriented_rows": sum(r["orbit_size"] for r in rs)}
        profiles = []
        for key in sorted({(tuple(r["sorted_singletons"]), sum(r["t"])) for r in nr}):
            before = [r for r in nr if (tuple(r["sorted_singletons"]), sum(r["t"])) == key]
            after = [r for r in before if r["passes_b4_arithmetic"]]
            profiles.append({"s_sorted": list(key[0]), "T": key[1],
                             "base": counts(before), "after_B4": counts(after)})
        summaries[str(N)] = {"base": counts(nr), "after_B4": counts(surviving),
                            "common_triangle_terminal_guard": counts(
                                [r for r in surviving if r["common_triangle_terminal_guard"]]),
                            "triangle_row_capacity_contradiction": counts(
                                [r for r in surviving if r["triangle_propagation"]
                                 ["triangle_row_capacity_contradiction"]]),
                            "complete_P9_complement_guard": counts(
                                [r for r in surviving if r["complete_P9_complement_guard_witnesses"]]),
                            "triple_triangle_point_overload": counts(
                                [r for r in surviving if r["triple_triangle_point_overload"]]),
                            "after_stated_ordinary_exclusions": counts(
                                [r for r in surviving if not r["common_triangle_terminal_guard"]
                                 and not r["triangle_propagation"]["triangle_row_capacity_contradiction"]
                                 and not r["complete_P9_complement_guard_witnesses"]
                                 and not r["triple_triangle_point_overload"]]),
                            "profiles": profiles}
    return {
        "schema": "cap15-mu41-N45plus-arithmetic-signatures-v1",
        "scope": "necessary arithmetic signatures; surviving rows need not be geometrically realizable",
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "pair_order": [list(p) for p in PAIRS], "triple_index": "omitted root point",
        "assumptions": {"global_degree_cap": 15, "singleton_cap": 9,
                        "three_largest_singletons_sum_cap": 26, "minimum_neighbourhood": 41,
                        "target_neighbourhood_min": 45, "pair_trace_cap": 3,
                        "triple_trace_cap": 1, "global_pair_codegree_cap": 6},
        "sorted_singleton_candidates": [list(s) for s in possible_s],
        "summaries": summaries, "records": records,
    }


if __name__ == "__main__":
    result = census()
    path = HERE / "LOW15-high-profile-census.json"
    path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"output": str(path), "summaries": result["summaries"]}, indent=2))
