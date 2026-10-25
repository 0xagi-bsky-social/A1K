#!/usr/bin/env python3
"""Replay one hash-bound degree17 full-model integer-box certificate without a solver.

Supports trace-objective upper bounds (<51) and explicitly tagged zero-objective
infeasibility certificates (<0), using their unchanged hash-matched producer
build(). The frozen original and v2/v3/v4/v5/v6 are selected by exact SHA256, never by
assuming that the current source equals the receipt source. All eleven root
geometries, literal premises, dependencies, boxes and matrix entries are checked.
P10 cases additionally bind the twelve separately completed component replays.
Generic triangle rows are re-derived using actual-point sets and checked in full.
For v3/v4 the optional clique file and its source dependencies are hash-bound;
literal H27 compatibility, every diagonal, the one permitted trace refinement,
and every clique coefficient/RHS are reconstructed independently of its loader.
For v4 all literal B4 witnesses and singleton-cap rows are decoded independently;
final local-selector feature equations verify the surviving singleton pruning.
For v5, literal extra actual members and their represented support are decoded
independently; exact trace boxes and all fixed-anchor rows are checked, and
triangle/B4/H27 verification uses the full selected actual family.
For v6, a direct independent two-avoidance table on the actual P9/P10
root cones establishes the whole zero-or-one-Y residual clique, including
all diagonal classes, before its full sparse row and RHS are checked.

This is shared-producer model reconstruction and exact arithmetic replay. It is
not independent model reconstruction, a proof of imported mathematical premises,
Lean verification, or a complete branch proof. One case only, at most 30 seconds.
"""

import argparse
import hashlib
import importlib.util
import inspect
import itertools
import json
import math
import os
from pathlib import Path
import re
import signal
import sys
import time

sys.dont_write_bytecode = True
for thread_variable in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[thread_variable] = "1"
HERE = Path(__file__).resolve().parent
CASE_KEYS = ("kind", "case", "empty_z", "assigned_z", "forbidden",
             "forbid_four_core", "degree_distributions", "crowding_imports")

EXPECTED_KINDS = tuple(f"P10-H{i}" for i in range(8)) + ("P9-P8-i1", "P9-P8-i2", "P9-Q8")
V6_SOURCE_SHA256 = "8f43465ef15e09ba5ea8f472a4382f844ccb3ebeface8841f7963625f65e8138"
V6_PHASEONE_SHA256 = "dbd6cc300ab8a94b060521e868786359152327486d781eace448dda968730967"
SUPPORTED_SOURCES = {
    "3d79ea4a0755f59aa8107c89d773600bc0965aa751772c337c3431c3a7caff52": False,
    "497f71f4fdf555c7456b42123684e7fd5059769f89662c257e2263425798b31a": True,
    "d247fa0ac29e5ea765f5ede2d60df9ff9ce89e905f86f1295161acedceb370ae": True,
    "a1beae56f60205a48442a1c6a31d2148557443511fb119a1936ffda8578bebf2": True,
    "bee8278d87557a3f979d7c69022d62d775e74f093cb87ece2c935e6f1acd1210": True,
    V6_SOURCE_SHA256: True,
}
H27_SOURCES = {"d247fa0ac29e5ea765f5ede2d60df9ff9ce89e905f86f1295161acedceb370ae",
               "a1beae56f60205a48442a1c6a31d2148557443511fb119a1936ffda8578bebf2",
               "bee8278d87557a3f979d7c69022d62d775e74f093cb87ece2c935e6f1acd1210",
               V6_SOURCE_SHA256}
B4_SOURCES = {"a1beae56f60205a48442a1c6a31d2148557443511fb119a1936ffda8578bebf2",
              "bee8278d87557a3f979d7c69022d62d775e74f093cb87ece2c935e6f1acd1210",
              V6_SOURCE_SHA256}
EXTRA_SOURCES = {"bee8278d87557a3f979d7c69022d62d775e74f093cb87ece2c935e6f1acd1210",
                 V6_SOURCE_SHA256}
PHASEONE_ADAPTERS = {
    "929a101c2ec29570790450d112914f2048a83c78fdf8b5f658f84cb7f4eb8069": "degree17_full_phaseone.py",
    "957d9fd1e1fa162a3f3a18a1937a5cc613078552c4ca607dc76c60d67cb568f8": "degree17_full_phaseone_v5.py",
    V6_PHASEONE_SHA256: "degree17_full_phaseone_v6.py",
}
PHASEONE_MODEL_SOURCES = {
    "929a101c2ec29570790450d112914f2048a83c78fdf8b5f658f84cb7f4eb8069":
        set(SUPPORTED_SOURCES) - EXTRA_SOURCES,
    "957d9fd1e1fa162a3f3a18a1937a5cc613078552c4ca607dc76c60d67cb568f8":
        {"bee8278d87557a3f979d7c69022d62d775e74f093cb87ece2c935e6f1acd1210"},
    V6_PHASEONE_SHA256: {V6_SOURCE_SHA256},
}
H27_TRANSFER_POLICY = "same universe, or root-only core-to-one-marker restriction lift; literal pair validation required"
P10_COMPONENT_SOURCE_SHA256 = "1e3eaa89225246bb695740792bcaf0a5c365eb50c4212467aeb3c9569d7658d0"
P10_COMPONENT_REPLAYER_SHA256 = "1e6ef9e322b31593e12483a1e53937bf950f424d8c29433793f40ed98198608a"
P10_REPLAY_SUMMARY_SHA256 = "d130fb5c8f164e4ab6a164e60bd1c2e8f41021da82f48195255a3cc11690711c"
P10_COMPONENT_BRIDGES = {"D17-research.md", "D18-R99-bridge.md",
                         "D19-singleton-I04.md", "C5-internal-compatibility.md"}


class ReplayError(ValueError):
    pass


class ReplayTimeout(TimeoutError):
    pass


def require(condition, message):
    if not condition:
        raise ReplayError(message)


def integer(value, name):
    require(type(value) is int, f"{name} must be a JSON integer, not bool/float")
    return value


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def digest_value(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"),
                                     allow_nan=False).encode()).hexdigest()


def primitive(value):
    return json.loads(json.dumps(value, allow_nan=False))


def digest_string(value, name):
    require(isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value),
            f"{name} must be a complete lowercase SHA256")
    return value


def source_candidates(choice):
    frozen = sorted(HERE.glob("degree17_full_projection_v*.py"),
                    key=lambda p: int(re.search(r"_v([0-9]+)\.py$", p.name).group(1))
                    if re.search(r"_v([0-9]+)\.py$", p.name) else -1)
    frozen = [p for p in frozen if re.search(r"_v[0-9]+\.py$", p.name)]
    current = HERE / "degree17_full_projection.py"
    if choice == "auto":
        return frozen + [current]
    if choice == "current":
        return [current]
    require(bool(re.fullmatch(r"v[1-9][0-9]*", choice)), "Invalid --source selector")
    return [HERE / f"degree17_full_projection_{choice}.py"]



def bind_p10_exclusion(receipt, kwargs, bind_file, local_sha):
    """Bind saved component replays; do not execute or re-replay their models."""
    imported = receipt.get("P10_internal_exclusion_receipts", {})
    if not kwargs["kind"].startswith("P10-"):
        require(not imported, "P9 branch must not import P10 internal emptiness")
        return {"required": False, "reason": "P9-side internals remain free"}
    expected_names = {f"P10_{i:03d}.json" for i in range(1, 13)}
    require(isinstance(imported, dict) and set(imported) == expected_names,
            "P10 branch must identify all twelve nonempty component receipts")
    summary_path = HERE / "degree17-replay/P10-nonempty-summary.json"
    summary_bound = bind_file(summary_path, P10_REPLAY_SUMMARY_SHA256, "P10 exact-replay summary")
    summary = json.loads(summary_path.read_text())
    require(summary.get("all_pass") is True and integer(summary.get("count"), "P10 summary count") == 12,
            "P10 summary is not a twelve-case successful replay")
    rows = summary.get("records")
    require(isinstance(rows, list) and len(rows) == 12, "Invalid P10 replay summary records")
    by_name = {}
    for row in rows:
        require(isinstance(row, dict) and isinstance(row.get("receipt"), str), "Malformed P10 summary record")
        name = Path(row["receipt"]).name
        require(name in expected_names and name not in by_name, "Duplicate/unknown P10 summary case")
        by_name[name] = row
    require(set(by_name) == expected_names, "Incomplete P10 replay coverage")
    component_source = bind_file(HERE / "degree17_component.py", P10_COMPONENT_SOURCE_SHA256,
                                 "P10 component source")
    component_replayer = bind_file(HERE / "replay_component17.py", P10_COMPONENT_REPLAYER_SHA256,
                                   "P10 component replayer")
    records, orbit_total = [], 0
    prior = HERE.parents[1] / "frontier20261020/prior-art68"
    for name in sorted(expected_names):
        item, saved = imported[name], by_name[name]
        require(isinstance(item, dict) and set(item) == {"sha256", "recorded_gap", "status"},
                "Malformed imported P10 component record")
        require(item["status"] == "imported recorded exact gap; not independently replayed by this script",
                "P10 producer record changed its assurance tag")
        original_path = (HERE / "degree17" / name).resolve()
        replay_path = (HERE / "degree17-replay" / (Path(name).stem + "-replay.json")).resolve()
        require(saved.get("receipt") == str(original_path) and saved.get("replay") == str(replay_path)
                and saved.get("result") == "PASS", "P10 summary paths/status differ")
        require(saved.get("receipt_sha256") == item["sha256"], "P10 summary and producer bind different inputs")
        original_bound = bind_file(original_path, item["sha256"], "P10 input " + name)
        replay_bound = bind_file(replay_path, saved.get("replay_sha256"), "P10 replay " + name)
        old, evidence = json.loads(original_path.read_text()), json.loads(replay_path.read_text())
        require(evidence.get("result") == "PASS" and evidence.get("all_bound_inputs_unchanged") is True,
                "P10 component replay is not an unchanged-input PASS")
        require(evidence.get("receipt_path") == str(original_path)
                and evidence.get("receipt_sha256") == original_bound["sha256"]
                and evidence.get("replayer_sha256") == P10_COMPONENT_REPLAYER_SHA256,
                "P10 exact replay has the wrong original input or checker")
        require(integer(old.get("status"), "P10 original status") == 0,
                "P10 component input is not a completed phase-one receipt")
        for field, expected in (("root_degree", 17), ("point_cap", 17), ("mu", 41), ("min_used_degree", 7)):
            require(integer(old.get(field), "P10 " + field) == expected, "P10 component scope differs")
        case = old.get("case")
        require(isinstance(case, dict) and case.get("id") + ".json" == name
                and case.get("component") == 10 and case.get("outside") == 7
                and case.get("r10") == 0 and case.get("r9") == 0
                and isinstance(case.get("interiors"), list) and bool(case["interiors"]),
                "Wrong/nonempty P10 component case")
        require(evidence.get("case") == case, "P10 replay case differs from its input")
        require(old.get("source_sha256") == P10_COMPONENT_SOURCE_SHA256
                and evidence.get("source", {}).get("sha256") == P10_COMPONENT_SOURCE_SHA256
                and Path(evidence["source"]["path"]).resolve() == Path(component_source["path"]),
                "P10 component source differs")
        require(old.get("local43_sha256") == local_sha
                and evidence.get("local43", {}).get("sha256") == local_sha
                and evidence.get("local43", {}).get("match") is True,
                "P10 component local43 differs from full-model import")
        pinned, ordinary = old.get("pinned_dependencies"), old.get("ordinary_bridge_sha256")
        require(isinstance(pinned, dict) and isinstance(ordinary, dict)
                and set(ordinary) == P10_COMPONENT_BRIDGES, "P10 dependency registries are malformed")
        require(evidence.get("dependencies", {}).get("pinned") == pinned
                and evidence.get("dependencies", {}).get("ordinary_bridge_sha256") == ordinary,
                "P10 replay bound different proof dependencies")
        for relative, digest in pinned.items():
            require(isinstance(relative, str) and not Path(relative).is_absolute()
                    and ".." not in Path(relative).parts, "Invalid P10 prior dependency path")
            bind_file(prior / relative, digest, "P10 prior " + relative)
        for filename, digest in ordinary.items():
            bind_file(HERE / filename, digest, "P10 ordinary " + filename)
        literal = evidence.get("literal_premises")
        require(isinstance(literal, dict)
                and literal.get("family") == "finite simple SF4, empty-core sunflowers forbidden, cardinality exactly 68"
                and literal.get("global_degree_cap") == 17
                and literal.get("minimum_closed_neighborhood") == 41
                and literal.get("minimum_used_degree") == 7
                and literal.get("complete_centre_link") == "P10 plus a disjoint-support intersecting family of 7 triples"
                and literal.get("bootstrap") == {"r10": 0, "r9": 0}, "P10 literal scope differs")
        premise = digest_value(dict(source_sha256=P10_COMPONENT_SOURCE_SHA256, case=case,
                                    root_degree=17, point_cap=17, mu=41, min_used_degree=7,
                                    cardinality=68, pinned_dependencies=pinned,
                                    ordinary_bridge_sha256=ordinary, literal_premises=literal))
        require(evidence.get("premise_sha256") == premise, "P10 exact replay premise hash differs")
        exact, cert = evidence.get("exact"), old.get("certificate")
        require(isinstance(exact, dict) and isinstance(cert, dict), "Missing P10 exact arithmetic")
        for key in ("scale", "H", "minimum", "G"):
            require(integer(exact.get(key), "P10 replay " + key) == integer(cert.get(key), "P10 certificate " + key),
                    "P10 exact scalar mismatch: " + key)
        require(exact["scale"] > 0 and exact["G"] == exact["H"] - exact["minimum"]
                and exact["G"] < 0 and exact.get("negative") is True and cert.get("negative") is True
                and integer(item["recorded_gap"], "imported P10 gap") == exact["G"]
                and exact.get("source_weights_nonnegative") is True,
                "P10 replay does not certify a strict zero-objective contradiction")
        require(integer(exact.get("q_column_count"), "P10 q columns") == integer(old.get("columns"), "P10 columns"),
                "P10 exact replay column coverage differs")
        digest_string(exact.get("q_sha256_decimal_lines"), "P10 coefficient vector hash")
        model = evidence.get("model", {})
        for key in ("columns", "upper_rows", "equal_rows"):
            require(integer(model.get(key), "P10 replay model " + key) == old[key], "P10 model dimensions differ")
        model_digest = digest_string(model.get("sha256"), "P10 model hash")
        catalogue = evidence.get("catalogue", {})
        require(catalogue.get("internal_count") == 292 and catalogue.get("automorphism_count") == 60
                and catalogue.get("orbit_count") == 13, "P10 full internal catalogue differs")
        orbit_total += integer(catalogue.get("orbit_size"), "P10 orbit size")
        records.append(dict(case=case["id"], original=original_bound, replay=replay_bound,
                            premise_sha256=premise, model_sha256=model_digest, exact_gap=exact["G"],
                            orbit_size=catalogue["orbit_size"]))
    require(orbit_total == 291, "The twelve P10 nonempty orbits do not cover 291 assignments")
    return dict(required=True, summary=summary_bound, component_source=component_source,
                component_replayer=component_replayer, nonempty_orbits=12, nonempty_assignments=291,
                records=records,
                scope="existing separately completed shared-model exact replays are hash-bound, not rerun here; exact68-to-at-least68 transfer is the ordinary subfamily argument in D17-full-model-bridge.md")


def selected_actual_masks(geometry, kwargs):
    """Independently order the actual residual members, without producer helpers."""
    marker = geometry["records"][kwargs["case"]]["marker"]
    extras = kwargs.get("extra_members", [])
    require(isinstance(extras, list) and all(type(v) is int and v >= 0 for v in extras)
            and extras == sorted(set(extras)), "Extra actual masks must be sorted distinct integers")
    selected = ([] if marker is None else [marker]) + extras + (kwargs["assigned_z"] or [])
    selected = tuple(dict.fromkeys(selected))
    core = frozenset(geometry["Y"] + geometry["Z"])
    root = integer(geometry["root"], "selected root")
    extra_point = integer(geometry["exterior_marker"], "canonical extra point")
    require(root == 15 and core == frozenset(range(len(core))) and extra_point == len(core),
            "Selected member geometry is not the complete canonical core")
    allowed = core | {extra_point}
    for member in selected:
        require(type(member) is int and member >= 0, "Actual member mask must be a nonnegative integer")
        block = frozenset(v for v in range(member.bit_length()) if member >> v & 1)
        require(len(block) == 4 and block <= allowed and root not in block,
                "Selected member is not a residual four-set on core plus its one canonical extra point")
    return selected


def extra_member_metadata(receipt, geometry, kwargs, required):
    fields = ("extra_members", "selected_actual_members", "represented_points")
    if not required:
        require(not any(key in receipt for key in fields), "Older producer has unexpected extra-member metadata")
        return dict(required=False)
    selected = selected_actual_masks(geometry, kwargs)
    core = frozenset(geometry["Y"] + geometry["Z"])
    represented = set(core)
    for member in selected:
        represented.update(v for v in range(member.bit_length()) if member >> v & 1)
    require(represented == set(range(len(represented))) and len(core) <= len(represented) <= len(core) + 1,
            "Selected actual support is not the permitted canonical refinement")
    require(receipt.get("extra_members") == kwargs["extra_members"]
            and receipt.get("selected_actual_members") == list(selected)
            and receipt.get("represented_points") == sorted(represented),
            "Recorded extra actual members or full represented support differs")
    stars = tuple((1 << 15) | t for t in geometry["link"])
    fixed = stars + selected
    require(not any(A & B == A & C == B & C for A, B, C in itertools.combinations(fixed, 3)),
            "Declared fixed actual members already form a sunflower")
    return dict(required=True, extra_members=list(kwargs["extra_members"]),
                selected_actual_members=list(selected), represented_points=sorted(represented),
                fixed_actual_member_count=len(fixed),
                scope="independent literal selected-set normalization and support reconstruction")


def validate_extra_member_rows(traces, bounds, A, b, labels, geometry, kwargs, metadata, check_time):
    """Independently check trace boxes and the full actual-anchor row coverage."""
    if not metadata["required"]:
        return metadata

    def pointset(value):
        return frozenset(v for v in range(value.bit_length()) if value >> v & 1)

    def setmask(values):
        return sum(1 << v for v in values)

    def sparse_row(row):
        actual = {}
        for p in range(A.indptr[row], A.indptr[row + 1]):
            j, value = int(A.indices[p]), int(A.data[p])
            actual[j] = actual.get(j, 0) + value
        return {j: v for j, v in actual.items() if v}

    represented = metadata["represented_points"]
    expected_traces = tuple(setmask(U) for size in range(5)
                            for U in itertools.combinations(represented, size))
    require(tuple(traces) == expected_traces, "v5 trace domain/order differs from selected actual support")
    selected = selected_actual_masks(geometry, kwargs)
    stars = tuple((1 << 15) | t for t in geometry["link"])
    fixed = stars + selected
    star_sets = tuple(map(pointset, stars))
    fixed_sets = {member: pointset(member) for member in fixed}
    trace_sets = tuple(map(pointset, traces))
    y, z = frozenset(geometry["Y"]), frozenset(geometry["Z"])
    core = y | z
    forbidden = set(kwargs["forbidden"])
    require(forbidden <= set(traces), "Forbidden trace is outside the represented universe")
    assigned = kwargs["assigned_z"]
    assigned_set = set(assigned or [])
    if assigned is not None:
        require(all(len(pointset(t)) == 4 and pointset(t) <= z for t in assigned),
                "Assigned-Z pattern has a noninternal member")
        require(not kwargs["empty_z"] or not assigned, "Assigned-Z pattern conflicts with emptiness")
    relevant = [(fixed_sets[a], fixed_sets[c]) for a, c in itertools.combinations(fixed, 2)
                if not (15 in fixed_sets[a] and 15 in fixed_sets[c])]
    expected_boxes = []
    for s, S in zip(traces, trace_sets):
        lo, hi = 0, {0: 27, 1: 17, 2: 6, 3: 2, 4: 1}[len(S)]
        if len(S) == 4:
            if (kwargs["kind"].startswith("P10-") and S <= y) or (kwargs["empty_z"] and S <= z):
                hi = 0
            if assigned is not None and S <= z:
                lo = hi = int(s in assigned_set)
            if kwargs["forbid_four_core"] and S <= core:
                hi = 0
        if s in forbidden:
            hi = 0
        if s in selected:
            lo = 1
        if any(S & B == S & C == B & C for B, C in relevant):
            hi = 0
        require(lo <= hi, "Selected actuals conflict with exact absence or sunflower bounds")
        expected_boxes.append((lo, hi))
    require([(int(lo), int(hi)) for lo, hi in bounds[:len(traces)]] == expected_boxes,
            "v5 exact trace boxes differ from literal actual-family reconstruction")
    require(all(bounds[traces.index(member)] == (1, 1) for member in selected),
            "Selected actual member lacks its literal membership box")
    expected = {}

    def add(label, coefficients, rhs):
        require(label not in expected, "Duplicate independently derived actual-anchor row")
        expected[label] = ({j: w for j, w in coefficients.items() if w}, rhs)

    for anchor in fixed:
        R = fixed_sets[anchor]
        add(("disjoint-H27", anchor), {j: 1 for j, S in enumerate(trace_sets) if S.isdisjoint(R)},
            27 - sum(B.isdisjoint(R) for B in star_sets))
        add(("actual-anchor-mu41", anchor), {j: -1 for j, S in enumerate(trace_sets) if S & R},
            sum(bool(B & R) for B in star_sets) - 41)
        for size, cap in ((1, 10), (2, 3), (3, 1)):
            for values in itertools.combinations(sorted(R), size):
                U = frozenset(values)
                add(("exact-anchor", anchor, setmask(U)),
                    {j: 1 for j, S in enumerate(trace_sets) if S & R == U},
                    cap - sum(B & R == U for B in star_sets))
        for u, v in itertools.combinations(sorted(R), 2):
            add(("actual-anchor-pair19", anchor, u, v),
                {j: -int(u in S)-int(v in S) for j, S in enumerate(trace_sets)},
                sum(int(u in B)+int(v in B) for B in star_sets) - 19)
        if kwargs["crowding_imports"]:
            for values in itertools.combinations(sorted(R), 3):
                singles = tuple(frozenset((v,)) for v in values)
                add(("imported-crowding26", anchor, values),
                    {j: 1 for j, S in enumerate(trace_sets) if S & R in singles},
                    26 - sum(B & R in singles for B in star_sets))
        check_time()
    prefixes = {label[0] for label in expected}
    seen = set()
    for i, label in enumerate(labels):
        if not label or label[0] not in prefixes:
            continue
        key = tuple(tuple(v) if isinstance(v, (list, tuple)) else v for v in label)
        require(key in expected and key not in seen, "Unexpected/duplicate v5 actual-anchor row")
        terms, rhs = expected[key]
        require(sparse_row(i) == terms and int(b[i]) == rhs,
                "v5 actual-anchor coefficients or fixed-root offsets differ")
        seen.add(key)
    require(seen == set(expected), "v5 does not constrain every selected actual anchor")
    return dict(metadata, trace_domain_checked=True, all_trace_boxes_checked=True,
                selected_membership_boxes_checked=True, fixed_anchor_rows_checked=len(expected),
                fixed_anchor_rows_sha256=digest_value([
                    dict(label=label, coefficients=sorted(terms.items()), rhs=rhs)
                    for label, (terms, rhs) in expected.items()]),
                root_only_offsets_checked=True,
                scope="independent literal support, trace domain/boxes, selected membership and all fixed-anchor cap/mu41/pair19/crowding/disjoint-H27 rows; triangle/B4/H27 clique validations are separate")


def validate_triangle_rows(traces, A, b, labels, geometry, kwargs, required, check_time):
    """Independently decode literal sets and check every generic triangle row."""
    row_numbers = [i for i, label in enumerate(labels)
                   if isinstance(label, (list, tuple)) and label and label[0] == "two-actual-anchor-triangle"]
    if not required:
        require(not row_numbers, "Original source unexpectedly has v2 triangle rows")
        return {"required": False, "rows": 0, "scope": "frozen original lacks this strengthening"}
    root = integer(geometry.get("root"), "geometry root")
    require(root == 15, "Unexpected root label")

    def pointset(value):
        require(type(value) is int and value >= 0, "Invalid actual-point mask")
        return frozenset(i for i in range(value.bit_length()) if value & (1 << i))

    def setmask(values):
        return sum(1 << v for v in values)

    stars = tuple((1 << root) | t for t in geometry["link"])
    star_sets = tuple(pointset(t) for t in stars)
    selected = selected_actual_masks(geometry, kwargs)
    fixed = stars + selected
    require(len(fixed) == len(set(fixed)), "Fixed actual members repeat")
    fixed_sets = {t: pointset(t) for t in fixed}
    trace_sets = tuple(pointset(t) for t in traces)
    index = {t: i for i, t in enumerate(traces)}
    expected = {}
    for R, M in itertools.permutations(fixed, 2):
        rset, mset = fixed_sets[R], fixed_sets[M]
        shared = rset & mset
        if len(shared) != 2:
            continue
        for m in sorted(shared):
            h = next(iter(shared - {m}))
            for k in sorted(rset - mset):
                companion_set = (mset - {h}) | {k}
                companion = setmask(companion_set)
                label = ("two-actual-anchor-triangle", R, M, h, m, k, companion)
                require(len(rset | mset) == 6 and len(companion_set) == 4,
                        "Triangle hypothesis does not give six distinct labels")
                singleton, pair = frozenset({m}), frozenset({m, k})
                terms = {j: 1 for j, u in enumerate(trace_sets) if u & rset in (singleton, pair)}
                offset = sum(u & rset in (singleton, pair) for u in star_sets)
                rhs, companion_kind = 12 - offset, "residual"
                if root in companion_set:
                    membership = int(companion_set in star_sets)
                    rhs += membership
                    companion_kind = "root-present" if membership else "root-absent"
                else:
                    require(companion in index, "Residual companion has no full-four trace")
                    j = index[companion]
                    require(terms.get(j) == 1, "Residual companion must lie in the exact pair category")
                    del terms[j]
                require(label not in expected, "Duplicate mathematical triangle label")
                expected[label] = terms, rhs, companion_kind, offset
        check_time()
    require(len(row_numbers) == len(expected), "Generic triangle row coverage differs")
    seen, companion_counts = set(), {"root-present": 0, "root-absent": 0, "residual": 0}
    offset_counts = {}
    for i in row_numbers:
        label = tuple(labels[i])
        require(label in expected and label not in seen, "Unexpected/duplicate generic triangle row")
        terms, rhs, kind, offset = expected[label]
        actual = {int(A.indices[p]): int(A.data[p]) for p in range(A.indptr[i], A.indptr[i+1]) if A.data[p]}
        require(actual == terms and int(b[i]) == rhs, "Triangle coefficient or fixed-offset mismatch")
        seen.add(label)
        companion_counts[kind] += 1
        offset_counts[str(offset)] = offset_counts.get(str(offset), 0) + 1
        check_time()
    require(seen == set(expected), "Missing generic triangle inequality")
    return dict(required=True, rows=len(expected), companion_counts=companion_counts,
                fixed_offset_counts=offset_counts,
                scope="all fixed actual ordered pairs and both m/k choices decoded with point sets; every full sparse coefficient and RHS checked; no independent verification of other producer rows")


def bind_h27_input(receipt, enabled, bind_file):
    """Reproduce v3's dependency record without calling its input helper."""
    if not enabled:
        require("h27_cliques" not in receipt, "Older source has unexpected v3 clique metadata")
        return None, None
    require("h27_cliques" in receipt, "v3 must explicitly record its optional clique dependency")
    dep = receipt["h27_cliques"]
    if dep is None:
        return None, None
    keys = {"path", "sha256", "schema", "source_kind", "source_case", "represented_points",
            "excluded_points", "fixed_members", "clique_row_count", "sources", "transfer_policy"}
    require(isinstance(dep, dict) and set(dep) == keys, "Malformed v3 H27 dependency dictionary")
    require(isinstance(dep["path"], str) and Path(dep["path"]).is_absolute(),
            "H27 dependency path must be absolute")
    path = Path(dep["path"]).resolve()
    require(str(path) == dep["path"], "H27 dependency path must be canonical")
    bound = bind_file(path, dep["sha256"], "H27 literal row data")
    data = json.loads(path.read_bytes())
    require(isinstance(data, dict) and data.get("schema") == "trace-h27-clique-discovery-v1",
            "Unsupported H27 discovery data schema")
    require(integer(data.get("threshold"), "H27 threshold") == 27, "H27 threshold must equal27")
    require(isinstance(data.get("clique_rows"), list) and data["clique_rows"],
            "H27 data must contain an explicit nonempty list of rows")
    sources = {}
    for key, filename in (("separator_source_sha256", "trace_h27_cliques.py"),
                          ("ordinary_note_sha256", "TRACE-H27-CLIQUE-SEPARATION.md")):
        sources[key] = bind_file(HERE / filename, data.get(key), "H27 " + filename)
    rebuilt = dict(path=bound["path"], sha256=bound["sha256"], schema=data["schema"],
                   source_kind=data.get("kind"), source_case=data.get("case"),
                   represented_points=data.get("represented_points"),
                   excluded_points=data.get("excluded_points"), fixed_members=data.get("fixed_members"),
                   clique_row_count=len(data["clique_rows"]), sources=sources,
                   transfer_policy=H27_TRANSFER_POLICY)
    require(dep == rebuilt, "H27 dependency metadata differs from bound row bytes and sources")
    return data, rebuilt


def validate_h27_rows(data, traces, A, b, labels, geometry, kwargs, check_time):
    """Independent set-based compatibility and complete fine-row reconstruction.

    A literal-set relation is computed on every source trace appearing in any
    row, including diagonals. Row bitsets then check every pair against that
    relation. This avoids repeating millions of identical set proofs and never
    trusts a producer witness cache, discovery weight, or validation digest.
    """
    actual_rows = [i for i, label in enumerate(labels) if isinstance(label, (tuple, list))
                   and label and label[0] == "external-literal-H27-trace-clique"]
    if data is None:
        require(not actual_rows, "No H27 input was declared but external clique rows exist")
        return dict(required=False, rows=0)
    root = integer(geometry.get("root"), "H27 receiving root")
    require(root == 15 and data.get("kind") == kwargs["kind"], "H27 root or geometry kind differs")

    def pointset(value, name):
        value = integer(value, name)
        require(value >= 0 and value.bit_length() <= root + 1, "H27 mask has an invalid point label")
        return frozenset(i for i in range(value.bit_length()) if value & (1 << i))

    def mask_of(values):
        return sum(1 << v for v in values)

    raw_points = data.get("represented_points")
    require(isinstance(raw_points, list)
            and all(type(v) is int and 0 <= v < root for v in raw_points)
            and raw_points == sorted(set(raw_points)), "Invalid H27 source represented-point list")
    require(data.get("excluded_points") == [root]
            and type(data["excluded_points"][0]) is int, "H27 excluded points differ from residual root")
    source_points = frozenset(raw_points)
    y, z = geometry.get("Y"), geometry.get("Z")
    require(isinstance(y, list) and isinstance(z, list)
            and all(type(v) is int and 0 <= v < root for v in y + z)
            and len(y + z) == len(set(y + z)), "Malformed receiving component supports")
    core = frozenset(y + z)
    require(core == frozenset(range(len(core))), "Receiving core labels are not canonical")
    link = geometry.get("link")
    require(isinstance(link, list) and len(link) == 17 and len(set(link)) == 17,
            "H27 receiving complete link must have17 distinct triples")
    link_sets = tuple(pointset(t, "H27 link mask") for t in link)
    require(all(len(T) == 3 and T <= core for T in link_sets), "H27 receiving cone support is invalid")
    star_sets = tuple(T | {root} for T in link_sets)
    stars = tuple(mask_of(B) for B in star_sets)
    marker = geometry["records"][kwargs["case"]]["marker"]
    selected = selected_actual_masks(geometry, kwargs)
    selected_sets = tuple(pointset(M, "H27 selected actual member") for M in selected)
    require(all(len(M) == 4 and root not in M for M in selected_sets), "Invalid H27 selected actual member")
    represented = core | (frozenset().union(*selected_sets) if selected_sets else frozenset())
    require(represented == frozenset(range(len(represented))), "Receiving represented labels are not canonical")
    extra = represented - core
    if extra:
        require(extra == {integer(geometry["exterior_marker"], "marker point")}
                and any(extra <= S for S in selected_sets),
                "Only the one canonical point in selected actual members may extend the core")
        if "extra_members" not in kwargs:
            require(marker is not None and extra <= pointset(marker, "actual marker"),
                    "A legacy branch can extend the core only by its actual marker")
    expected_traces = tuple(mask_of(U) for k in range(5)
                            for U in itertools.combinations(sorted(represented), k))
    require(tuple(traces) == expected_traces, "Receiving residual trace domain/order is incomplete")
    same = source_points == represented
    lifted = source_points == core and len(extra) == 1
    require(same or lifted, "Unsupported H27 trace-universe refinement/coarsening")
    witnesses = data.get("fixed_members")
    require(isinstance(witnesses, list)
            and all(type(B) is int for B in witnesses)
            and len(set(witnesses)) == len(witnesses), "Malformed H27 witness list")
    witness_sets = tuple(pointset(B, "H27 witness") for B in witnesses)
    fixed_actual = frozenset(star_sets + selected_sets)
    require(all(len(B) == 4 and B in fixed_actual and B <= source_points | {root}
                for B in witness_sets), "H27 witness is unavailable or contains an unrepresented point")
    if lifted:
        require(all(B in star_sets for B in witness_sets), "Marker lift may use only source root-cone witnesses")

    cliques, seen, union = [], set(), set()
    for row in data["clique_rows"]:
        require(isinstance(row, dict) and integer(row.get("upper"), "H27 row upper") == 27,
                "H27 row upper differs from27")
        raw = row.get("trace_masks")
        require(isinstance(raw, list) and raw and all(type(s) is int for s in raw)
                and len(raw) == len(set(raw)), "Invalid or duplicate H27 trace masks")
        for s in raw:
            U = pointset(s, "H27 trace")
            require(len(U) <= 4 and U <= source_points, "H27 trace leaves the source universe")
        clique = tuple(sorted(raw))
        require(clique not in seen, "Duplicate external H27 row")
        seen.add(clique)
        cliques.append(clique)
        union.update(clique)
    universe = tuple(sorted(union))
    sets = tuple(pointset(s, "H27 relation trace") for s in universe)
    position = {s: i for i, s in enumerate(universe)}
    adjacency = [0] * len(universe)
    shared_count = fixed_count = incompatible = 0
    for i, S in enumerate(sets):
        for j in range(i, len(sets)):
            T = sets[j]
            if S & T:
                shared_count += 1
            elif any(B.isdisjoint(S) and B.isdisjoint(T) for B in witness_sets):
                fixed_count += 1
            else:
                incompatible += 1
                continue
            adjacency[i] |= 1 << j
            adjacency[j] |= 1 << i
        check_time()
    fine_sets = tuple(pointset(t, "H27 fine trace") for t in traces)
    expected, pair_count = {}, 0
    row_sizes = []
    for number, clique in enumerate(cliques):
        selected_bits = sum(1 << position[s] for s in clique)
        require(all(selected_bits & ~adjacency[position[s]] == 0 for s in clique),
                f'H27 row{number} has an incompatible trace pair or diagonal')
        pair_count += len(clique) * (len(clique) + 1) // 2
        row_hash = hashlib.sha256(json.dumps(clique, separators=(",", ":")).encode()).hexdigest()
        coarse_sets = frozenset(pointset(s, "H27 coarse trace") for s in clique)
        terms = {j: 1 for j, U in enumerate(fine_sets) if U & source_points in coarse_sets}
        require(terms, "H27 row has no fine trace coefficients")
        label = ("external-literal-H27-trace-clique", number, row_hash)
        expected[label] = terms
        row_sizes.append(dict(source_traces=len(clique), fine_traces=len(terms)))
        check_time()
    require(len(actual_rows) == len(expected), "External H27 row coverage/count differs")
    seen = set()
    for i in actual_rows:
        label = tuple(labels[i])
        require(label in expected and label not in seen, "Unexpected/duplicate H27 row label")
        actual = {}
        for p in range(A.indptr[i], A.indptr[i+1]):
            j, value = int(A.indices[p]), int(A.data[p])
            actual[j] = actual.get(j, 0) + value
        actual = {j: value for j, value in actual.items() if value}
        require(actual == expected[label] and int(b[i]) == 27,
                "H27 coefficient, fine-trace lift, selector coefficient, or RHS differs")
        seen.add(label)
        check_time()
    require(seen == set(expected), "Missing H27 clique inequality")
    return dict(required=True, rows=len(expected), transfer="root-core-to-marker-restriction" if lifted else "same-universe",
                represented_points=sorted(represented), source_represented_points=raw_points,
                actual_witness_count=len(witness_sets), row_pair_checks_including_self=pair_count,
                relation_trace_count=len(universe), relation_shared_point_pairs=shared_count,
                relation_fixed_witness_pairs=fixed_count, relation_incompatible_pairs=incompatible,
                row_sizes=row_sizes, rows_sha256=digest_value([
                    dict(label=label, coefficients=sorted(terms.items()), rhs=27)
                    for label, terms in expected.items()]),
                scope="independent literal-set actual-witness/diagonal checks, complete restriction lift and every sparse H27 row coefficient/RHS; discovery weights and producer validation helper unused")



def validate_b4_rows_and_pruning(traces, bounds, A, b, E, f, labels, sizes,
                                 geometry, kwargs, required, check_time):
    """Decode literal sets, direct cap7 rows and final local feature equations.

    The producer's witness helper and cached local catalogue are not called.
    Pruning evidence checks every surviving selector, not completeness of the
    unpruned universal catalogue or unrelated pruning predicates.
    """
    prefix = "fixed-near-disjoint-B4-singleton7"
    direct_rows = [i for i, label in enumerate(labels)
                   if isinstance(label, (list, tuple)) and label and label[0] == prefix]
    if not required:
        require(not direct_rows, "An older source unexpectedly has v4 marked-B4 rows")
        return {"required": False, "rows": 0, "pruning_checked": False}

    def pointset(value):
        integer(value, "B4 actual-point mask")
        require(value >= 0, "Negative B4 mask")
        return frozenset(i for i in range(value.bit_length()) if value & (1 << i))

    def sparse_row(matrix, number):
        require(0 <= number < matrix.shape[0], "B4 local equation cursor outside matrix")
        result = {}
        for p in range(matrix.indptr[number], matrix.indptr[number + 1]):
            j, value = int(matrix.indices[p]), int(matrix.data[p])
            result[j] = result.get(j, 0) + value
        return {j: value for j, value in result.items() if value}

    root = integer(geometry.get("root"), "B4 root")
    require(root == 15 and len(geometry["link"]) == 17, "Unexpected B4 root geometry")
    stars = tuple((1 << root) | t for t in geometry["link"])
    star_sets = tuple(pointset(t) for t in stars)
    selected = selected_actual_masks(geometry, kwargs)
    fixed = stars + selected
    require(len(fixed) == len(set(fixed)), "Repeated B4 actual members")
    fixed_sets = {t: pointset(t) for t in fixed}
    trace_sets = tuple(pointset(t) for t in traces)
    require(all(len(block) == 4 for block in fixed_sets.values()), "B4 witness is not a four-set")
    guards, expected = {}, {}
    for anchor in fixed:
        aset = fixed_sets[anchor]
        for vertex in sorted(aset):
            singleton = frozenset({vertex})
            near = [(B, fixed_sets[B] - singleton) for B in fixed
                    if vertex in fixed_sets[B] and (fixed_sets[B] - singleton) & (aset - singleton)]
            witness = next(((B, C) for (B, bt), (C, ct) in itertools.combinations(near, 2)
                            if bt.isdisjoint(ct)), None)
            if witness is None:
                continue
            B, C = witness
            require(fixed_sets[B] & fixed_sets[C] == singleton
                    and fixed_sets[B] != fixed_sets[C], "Invalid reconstructed B4 witness")
            terms = {j: 1 for j, u in enumerate(trace_sets) if u & aset == singleton}
            offset = sum(u & aset == singleton for u in star_sets)
            label = (prefix, anchor, vertex, B, C)
            expected[label] = terms, 7 - offset
            guards[anchor, vertex] = dict(witness=[B, C], fixed_offset=offset)
        check_time()
    require(len(direct_rows) == len(expected), "Marked-B4 row coverage differs")
    seen = set()
    for i in direct_rows:
        label = tuple(labels[i])
        require(label in expected and label not in seen, "Unexpected or duplicate marked-B4 row")
        terms, rhs = expected[label]
        require(sparse_row(A, i) == terms and int(b[i]) == rhs,
                "Marked-B4 sparse coefficient or root-star offset differs")
        seen.add(label)
        check_time()
    require(seen == set(expected), "Missing marked-B4 row")

    # Local selectors are the final blocks of columns, one per root anchor.
    # Decode their normalized groups and seven feature equations directly from
    # E. This is independent of the producer's cached catalogues/alive masks.
    require(len(sizes) == len(stars) and all(type(k) is int and k >= 0 for k in sizes),
            "B4 local catalogue dimensions are malformed")
    trace_count, column_count = len(traces), len(bounds)
    local_start = column_count - sum(sizes)
    require(trace_count <= local_start <= column_count, "B4 selector block boundary is invalid")
    represented = set().union(*trace_sets)
    require(sorted(represented) == list(range(len(represented))) and root not in represented,
            "B4 represented point universe is not the producer's contiguous root-free universe")
    degree_count, cursor = {}, 0
    if kwargs["degree_distributions"]:
        used_degree_cols = set()
        for vertex in sorted(represented):
            terms = sparse_row(E, cursor)
            require(int(f[cursor]) == 1 and all(value == 1 for value in terms.values())
                    and all(trace_count <= j < local_start for j in terms)
                    and not (used_degree_cols & set(terms)), "Malformed global degree selector normalization")
            degree_count[vertex] = len(terms)
            used_degree_cols.update(terms)
            cursor += 2
        require(used_degree_cols == set(range(trace_count, local_start)),
                "Global degree selector columns do not fill the pre-local block")
    else:
        require(local_start == trace_count, "Unexpected degree selectors while switch is disabled")
    start = local_start
    decoded_hash, reports = hashlib.sha256(), []
    guarded_coordinates = guarded_root_anchors = 0
    for T, anchor, size in zip(geometry["link"], stars, sizes):
        tset = pointset(T)
        pts = sorted(tset)
        require(len(pts) == 3, "Local root block is not a triple")
        cols = tuple(range(start, start + size))
        colset = set(cols)
        require(sparse_row(E, cursor) == dict.fromkeys(cols, 1) and int(f[cursor]) == 1,
                "Local selector normalization differs from its recorded contiguous block")
        features = [frozenset(pair) for pair in itertools.combinations(pts, 2)]
        features += [tset] + [frozenset({v}) for v in pts]
        values = []
        for number, feature in enumerate(features):
            row_number = cursor + 1 + number
            # Every trace term has +1. All other terms belong to this local
            # selector block and are the negatives of integer feature values.
            terms = sparse_row(E, row_number)
            trace_terms = {j: 1 for j, u in enumerate(trace_sets) if u & tset == feature}
            require(int(f[row_number]) == 0
                    and {j: value for j, value in terms.items() if j < trace_count} == trace_terms
                    and all(j < trace_count or j in colset for j in terms),
                    "Local feature equation has wrong trace bucket, selector block or RHS")
            decoded = [-terms.get(j, 0) for j in cols]
            cap = 3 if number < 3 else 1 if number == 3 else 10
            require(all(0 <= value <= cap for value in decoded), "Local feature is outside its universal integer range")
            values.append(decoded)
        local_report = dict(anchor=anchor, selector_columns=size, first_column=start,
                            singleton_guards=[])
        for position, vertex in enumerate(pts):
            if (anchor, vertex) in guards:
                guarded_coordinates += 1
                singleton_values = values[4 + position]
                require(all(value <= 7 for value in singleton_values),
                        "A witnessed singleton>=8 survived the v4 local pruning")
                local_report["singleton_guards"].append(dict(
                    vertex=vertex, witness=guards[anchor, vertex]["witness"],
                    maximum_surviving_singleton=max(singleton_values, default=None)))
        if (anchor, root) in guards:
            guarded_root_anchors += 1
            root_singletons = sum(u & fixed_sets[anchor] == frozenset({root}) for u in star_sets)
            require(root_singletons <= 7 or size == 0,
                    "A root-witness contradiction retained a local selector")
            local_report["root_guard"] = dict(witness=guards[anchor, root]["witness"],
                                                exact_root_singletons=root_singletons)
        decoded_hash.update(json.dumps(dict(anchor=anchor, features=values),
                                       sort_keys=True, separators=(",", ":")).encode())
        decoded_hash.update(b"\n")
        reports.append(local_report)
        cursor += 8 + (sum(degree_count[v] for v in pts) if kwargs["degree_distributions"] else 0)
        start += size
        check_time()
    require(start == column_count and cursor == E.shape[0],
            "Local selector decoding does not account for the complete column/equation layout")
    return dict(required=True, rows=len(expected), literal_guard_count=len(guards),
                rows_sha256=digest_value([dict(label=label, coefficients=sorted(terms.items()), rhs=rhs)
                                         for label, (terms, rhs) in expected.items()]),
                pruning_checked=True, guarded_local_coordinates=guarded_coordinates,
                guarded_root_anchors=guarded_root_anchors, decoded_local_selector_columns=sum(sizes),
                decoded_feature_sha256=decoded_hash.hexdigest(), local_anchors=reports,
                scope="independent literal-set witnesses, complete cap7 row coefficients/root offsets, and every final local feature equation; every surviving witnessed singleton is <=7, including empty-block/root guards; universal catalogue completeness and unrelated pruning remain shared-producer/ordinary-proof dependencies")


def validate_y_at_most_one_h27(traces, A, b, labels, geometry, required, check_time):
    """Independently establish TwoAvoidance, then check the complete v6 row.

    The 22 avoidance witnesses cover all subsets of Y of size at most2.
    The 28 unordered pairs with repetition of the seven zero/singleton
    Y classes include every diagonal. Since each witness is an actual
    root cone on {root} union Y, it also avoids every represented or
    unrepresented exterior completion of these root-avoiding traces.
    No producer geometry helper, clique loader, or row builder is used.
    """
    row_numbers = [i for i, label in enumerate(labels)
                   if isinstance(label, (list, tuple)) and label
                   and label[0] == "Y-at-most-one-H27"]
    if not required:
        require(not row_numbers, "Pre-v6 source unexpectedly has the whole zero-or-one-Y row")
        return dict(required=False, rows=0)
    require(len(row_numbers) == 1, "v6 must contain exactly one whole zero-or-one-Y row")

    def pointset(value):
        require(type(value) is int and value >= 0, "Invalid literal trace or link mask")
        return frozenset(v for v in range(value.bit_length()) if value >> v & 1)

    def setmask(values):
        return sum(1 << v for v in values)

    root = integer(geometry.get("root"), "Y-avoidance root")
    yp = geometry.get("Y")
    require(isinstance(yp, list) and all(type(v) is int and v >= 0 for v in yp)
            and len(yp) == len(set(yp)) == 6 and root not in yp,
            "Y-avoidance needs six distinct points outside the actual root")
    yset = frozenset(yp)
    link = geometry.get("link")
    require(isinstance(link, list) and len(link) == len(set(link)) == 17,
            "Y-avoidance requires the recorded complete 17-link")
    link_sets = tuple(pointset(t) for t in link)
    require(all(len(t) == 3 and root not in t for t in link_sets),
            "An actual root-link block is not a root-avoiding triple")
    blocks = tuple(t for t in link_sets if t <= yset)
    kind = geometry.get("kind")
    expected = 10 if isinstance(kind, str) and kind.startswith("P10-") else 9
    require(kind in EXPECTED_KINDS and len(blocks) == expected,
            "Wrong prescribed P9/P10 block count for the whole-Y row")
    root_cones = {t | {root} for t in link_sets}

    witnesses, table = {}, []
    for size in range(3):
        for sub in itertools.combinations(sorted(yset), size):
            avoid = frozenset(sub)
            block = next((t for t in blocks if not t & avoid), None)
            require(block is not None, "The actual Y blocks fail literal TwoAvoidance")
            cone = block | {root}
            require(cone in root_cones and len(cone) == 4 and not cone & avoid,
                    "TwoAvoidance witness is not an actual avoiding root cone")
            witnesses[avoid] = cone
            table.append(dict(Y_points=list(sub), actual_root_cone=setmask(cone)))
        check_time()
    require(len(witnesses) == 22, "Incomplete zero/one/two-point avoidance table")

    classes = (frozenset(),) + tuple(frozenset({v}) for v in sorted(yset))
    class_pairs = 0
    for left, right in itertools.combinations_with_replacement(classes, 2):
        cone = witnesses[left | right]
        require(not cone & left and not cone & right,
                "Literal Y-class pair, including diagonal, lacks an avoiding cone")
        class_pairs += 1
    require(class_pairs == 28, "Incomplete Y-class pair/diagonal coverage")

    trace_sets = tuple(pointset(t) for t in traces)
    require(all(root not in t for t in trace_sets),
            "The whole-Y residual row must exclude every root-containing trace")
    expected_terms = {j: 1 for j, t in enumerate(trace_sets) if len(t & yset) <= 1}
    require(bool(expected_terms), "The whole-Y residual clique is empty")
    # Only now inspect the claimed matrix row: no selector column, offset,
    # dropped zero-Y trace, or rounded fractional coefficient is accepted.
    row = row_numbers[0]
    require(tuple(labels[row]) == ("Y-at-most-one-H27",), "Malformed whole-Y row label")
    actual_terms = {}
    for p in range(A.indptr[row], A.indptr[row + 1]):
        column, value = int(A.indices[p]), float(A.data[p])
        require(math.isfinite(value) and value.is_integer(),
                "Nonintegral whole-Y row coefficient")
        actual_terms[column] = actual_terms.get(column, 0) + int(value)
    actual_terms = {j: value for j, value in actual_terms.items() if value}
    rhs = float(b[row])
    require(math.isfinite(rhs) and rhs == 27 and actual_terms == expected_terms,
            "Whole zero-or-one-Y row has wrong coefficients, selectors, or RHS")
    check_time()
    count = len(expected_terms)
    return dict(required=True, rows=1, actual_Y_blocks=len(blocks),
                two_avoidance_table=table, two_avoidance_table_sha256=digest_value(table),
                Y_classes=7, literal_class_pairs_including_diagonals=class_pairs,
                included_trace_columns=count,
                trace_pairs_including_diagonals_covered_by_table=count * (count + 1) // 2,
                root_cone_offset=0,
                row_sha256=digest_value(dict(label=["Y-at-most-one-H27"],
                                            coefficients=sorted(expected_terms.items()), rhs=27)),
                scope="independent actual-root-cone TwoAvoidance on all22 Y subsets, all28 zero/singleton class pairs including diagonals, and every full row coefficient/RHS; arbitrary exterior completions are covered by the root-avoiding trace lemma; H27 remains imported")


def replay(receipt_path, seconds=30, source_choice="auto"):
    started = time.monotonic()
    output = {
        "result": "STARTED", "receipt_path": str(receipt_path),
        "replayer_sha256": sha(__file__), "compute_limit_seconds": seconds,
        "python_executable": sys.executable, "python_version": sys.version,
        "assurance": "shared-producer necessary-model reconstruction and exact integer replay; mathematical premises remain imported; no solver, no Lean, no whole-branch claim",
    }
    tracked_files = {}
    solver_restore = []

    def check_time():
        if time.monotonic() - started >= seconds:
            raise ReplayTimeout("The one-case replay deadline expired")

    def alarm_handler(_signum, _frame):
        raise ReplayTimeout("The one-case replay deadline expired")

    def no_solver(*_args, **_kwargs):
        raise ReplayError("Solver or numerical producer invocation is forbidden during replay")

    def bind_file(path, expected, label):
        path = Path(path).resolve()
        expected = digest_string(expected, label)
        require(path.is_file() and sha(path) == expected, f"{label}: file hash mismatch")
        require(path not in tracked_files or tracked_files[path] == expected,
                f"{label}: inconsistent hashes for one dependency")
        tracked_files[path] = expected
        return {"path": str(path), "sha256": expected}

    previous_handler = signal.signal(signal.SIGALRM, alarm_handler)
    previous_timer = signal.getitimer(signal.ITIMER_REAL)
    signal.setitimer(signal.ITIMER_REAL, seconds)
    try:
        require(0 < seconds <= 30, "Replay deadline must be positive and at most 30 seconds")
        receipt_bytes = receipt_path.read_bytes()
        receipt_sha = hashlib.sha256(receipt_bytes).hexdigest()
        tracked_files[receipt_path] = receipt_sha
        output["receipt_sha256"] = receipt_sha
        receipt = json.loads(receipt_bytes)
        require(isinstance(receipt, dict), "Receipt must be a JSON object")
        require(integer(receipt.get("status"), "status") == 0,
                "Only successful receipts with stored exact weights are replayable")
        dual = receipt.get("dual")
        require(isinstance(dual, dict), "Missing integer dual certificate")
        certificate_kind = receipt.get("certificate_kind", "trace-upper-bound")
        require(certificate_kind in ("trace-upper-bound", "zero-infeasibility"),
                "Unknown certificate kind; objective must not be inferred from its sign")
        zero = certificate_kind == "zero-infeasibility"
        if zero:
            require(integer(receipt.get("original_status"), "original_status") == 2,
                    "Zero-infeasibility receipt must identify an original status-2 case")
            require(dual.get("objective") == "zero", "Zero certificate must explicitly set objective='zero'")
            original_path = Path(receipt.get("input_receipt_path", "")).resolve()
            require(original_path != receipt_path and original_path.parent == receipt_path.parent,
                    "Phase-one input must be a distinct original receipt in the same directory")
            output["original_receipt"] = bind_file(original_path, receipt.get("input_receipt_sha256"),
                                                   "phase-one original receipt")
            original = json.loads(original_path.read_text())
            require(integer(original.get("status"), "original input status") == 2,
                    "Phase-one input is not numerical status 2")
            changed_fields = {"status", "message", "assurance", "dual", "primal_trace"}
            for key, value in original.items():
                if key not in changed_fields:
                    require(key in receipt and receipt[key] == value,
                            f"Phase-one changed original model/premise metadata: {key}")
            phase_sha = receipt.get("certificate_producer_sha256")
            require(phase_sha in PHASEONE_ADAPTERS, "Unsupported frozen phase-one producer")
            require(receipt.get("source_sha256") in PHASEONE_MODEL_SOURCES[phase_sha],
                    "Phase-one adapter is not pinned to this model source/version")
            output["certificate_producer"] = bind_file(
                HERE / PHASEONE_ADAPTERS[phase_sha], phase_sha, "phase-one producer")
            output["original_metadata_preserved"] = True
        else:
            require(dual.get("objective", "trace") == "trace",
                    "Trace upper certificate has a conflicting objective tag")
            require("original_status" not in receipt and "below0" not in dual,
                    "Untagged phase-one metadata cannot be replayed as a trace objective")
        output["certificate_kind"] = certificate_kind
        output["objective"] = "all-zero" if zero else "one on trace columns, zero on selectors"

        wanted_sha = digest_string(receipt.get("source_sha256"), "projection source")
        require(wanted_sha in SUPPORTED_SOURCES, "Unsupported source SHA256; a new producer version needs an explicit adapter inspection")
        h27_enabled = wanted_sha in H27_SOURCES
        extras_enabled = wanted_sha in EXTRA_SOURCES
        matches = [p for p in source_candidates(source_choice)
                   if p.is_file() and sha(p) == wanted_sha]
        require(bool(matches), "No selected projection source exactly matches the receipt SHA256")
        source = matches[0]
        source_bytes = source.read_bytes()
        require(hashlib.sha256(source_bytes).hexdigest() == wanted_sha, "Source changed during selection")
        tracked_files[source.resolve()] = wanted_sha
        output["source"] = {"path": str(source), "sha256": wanted_sha,
                            "matching_paths": [str(p) for p in matches],
                            "reconstruction": "same hashed producer build(), never run()"}

        # Hash local43 before executing the known producer's import, then check
        # that its actual import resolves to exactly these pinned bytes.
        local_path = HERE.parents[1] / "frontier20261020/prior-art68/repository/companion/upstream/MU42/scripts/local43.py"
        dependencies = {"local43": bind_file(local_path, receipt.get("imported_local43_sha256"), "local43")}
        for key, filename in (("structural_note_sha256", "D18-structural-tools.md"),
                              ("pool_note_sha256", "D18-pool-research.md")):
            dependencies[key] = bind_file(HERE / filename, receipt.get(key), filename)
        spec = importlib.util.spec_from_file_location("degree17_full_exact_replay_model", source)
        require(spec is not None, "Cannot create producer module specification")
        model = importlib.util.module_from_spec(spec)
        exec(compile(source_bytes, str(source), "exec"), model.__dict__)
        model.run = no_solver
        model.main = no_solver
        require(Path(model.L.__file__).resolve() == local_path.resolve(), "Unexpected local43 import path")
        require(sha(model.L.__file__) == receipt["imported_local43_sha256"], "Imported local43 changed")
        import numpy as np
        import scipy
        import scipy.optimize as optimize
        output["dependency_versions"] = {"numpy": np.__version__, "scipy": scipy.__version__}
        for name in ("linprog", "milp"):
            if hasattr(optimize, name):
                solver_restore.append((optimize, name, getattr(optimize, name)))
                setattr(optimize, name, no_solver)

        require(integer(receipt.get("target_residuals"), "target_residuals") == 51,
                "Receipt must have residual target 51")
        require(integer(receipt.get("mu"), "mu") == 41 and
                integer(receipt.get("point_cap"), "point_cap") == 17,
                "Receipt must state mu41 and global point cap17")
        require(integer(receipt.get("root_degree"), "root_degree") == 17,
                "Receipt must state root degree17")
        require(model.ROOT_DEGREE == 17 and model.POINT_CAP == 17 and model.TARGET == 51
                and model.ROOT == 15 and tuple(model.KINDS) == EXPECTED_KINDS,
                "Producer constants or eleven root geometries differ from the supported D17 scope")
        require(all(key in receipt for key in CASE_KEYS), "Missing explicit branch or switch field")
        kwargs = {key: receipt[key] for key in CASE_KEYS}
        require(kwargs["kind"] in model.KINDS and isinstance(kwargs["case"], str), "Invalid component/marker kind")
        for key in ("empty_z", "forbid_four_core", "degree_distributions", "crowding_imports"):
            require(type(kwargs[key]) is bool, f"{key} must be a JSON boolean")
        for key in ("assigned_z", "forbidden"):
            values = kwargs[key]
            if key == "assigned_z" and values is None:
                continue
            require(isinstance(values, list), f"{key} must be a list of masks")
            for value in values:
                require(integer(value, key + " mask") >= 0, "Trace masks must be nonnegative")
            require(len(values) == len(set(values)), f"Repeated {key} masks")
        if extras_enabled:
            require("extra_members" in receipt, "v5 requires explicit extra actual members")
            kwargs["extra_members"] = receipt["extra_members"]
        expected_build_keys = (set(CASE_KEYS)
                               | ({"h27_cliques", "h27_cliques_sha256"} if h27_enabled else set())
                               | ({"extra_members"} if extras_enabled else set()))
        require(set(inspect.signature(model.build).parameters) == expected_build_keys,
                "This producer has an unsupported build signature; update the explicit replay adapter")
        require(kwargs["case"] in model.marker_catalogue(kwargs["kind"]), "Unknown marker case")
        clique_data, clique_dependency = bind_h27_input(receipt, h27_enabled, bind_file)
        premise_kwargs, build_kwargs = dict(kwargs), dict(kwargs)
        if h27_enabled:
            premise_kwargs["h27_cliques"] = clique_dependency
            build_kwargs.update(h27_cliques=None if clique_dependency is None else clique_dependency["path"],
                                h27_cliques_sha256=None if clique_dependency is None else clique_dependency["sha256"])
        actual_premises = primitive(model.premises(**premise_kwargs))
        require(receipt.get("literal_premises") == actual_premises, "Literal mathematical premises differ from producer")
        geometry = primitive(model.catalogue_metadata(kwargs["kind"]))
        require(receipt.get("geometry") == geometry, "Complete component/marker geometry differs from receipt")
        extra_metadata = extra_member_metadata(receipt, geometry, kwargs, extras_enabled)
        output["case"] = kwargs
        output["literal_premises"] = actual_premises
        output["geometry_sha256"] = digest_value(geometry)
        output["geometry_validation"] = "complete producer catalogue reproduced, including its exhaustive group/orbit coverage checks"
        output["h27_clique_dependency"] = clique_dependency

        recorded_imports = receipt.get("imported_crowding_sources", {})
        require(isinstance(recorded_imports, dict), "Imported dependency registry must be an object")
        if kwargs["crowding_imports"]:
            require(set(recorded_imports) == set(model.CROWDING_SOURCES), "Imported proof dependency names differ")
            for name, expected_path in model.CROWDING_SOURCES.items():
                item = recorded_imports[name]
                require(isinstance(item, dict) and set(item) == {"path", "sha256"},
                        f"Malformed imported dependency {name}")
                require(item["path"] == str(expected_path), f"Dependency path differs: {name}")
                dependencies[name] = bind_file(expected_path, item["sha256"], name)
        else:
            require(not recorded_imports, "Disabled crowding switch has unexpected imported dependencies")
        require(kwargs["crowding_imports"] is True, "D17 requires the explicit prior import package")
        p10_binding = bind_p10_exclusion(receipt, kwargs, bind_file,
                                         receipt["imported_local43_sha256"])
        output["P10_exclusion_binding"] = p10_binding
        output["dependencies"] = dependencies
        identity = dict(source_sha256=wanted_sha,
                        imported_local43_sha256=receipt["imported_local43_sha256"],
                        structural_note_sha256=receipt["structural_note_sha256"],
                        pool_note_sha256=receipt["pool_note_sha256"],
                        imported_crowding_sources=recorded_imports,
                        P10_internal_exclusion_receipts=receipt.get("P10_internal_exclusion_receipts", {}),
                        kind=kwargs["kind"], literal_premises=actual_premises)
        if h27_enabled:
            identity["h27_cliques"] = clique_dependency
        if extras_enabled:
            for key in ("extra_members", "selected_actual_members", "represented_points"):
                identity[key] = extra_metadata[key]
        premise_sha = digest_value(identity)
        require(digest_string(receipt.get("premise_sha256"), "premise identity") == premise_sha,
                "Stored premise fingerprint differs from rebuilt source/dependency/premise identity")
        output["premise_sha256"] = premise_sha
        output["replay_evidence_sha256"] = digest_value(dict(
            producer_premise_sha256=premise_sha, P10_exclusion_binding=p10_binding))

        check_time()
        traces, bounds, A, b, E, f, labels, sizes = model.build(**build_kwargs)
        A, E = A.tocsr(), E.tocsr()
        count, trace_count = len(bounds), len(traces)
        require(A.shape == (len(b), count) and E.shape == (len(f), count), "Invalid matrix shapes")
        require(len(labels) == len(b), "Upper-row label count mismatch")
        for key, value in (("columns", count), ("trace_columns", trace_count),
                           ("upper_rows", len(b)), ("equal_rows", len(f))):
            require(integer(receipt.get(key), key) == value, f"Rebuilt {key} differs from receipt")
        require(receipt.get("catalogue_sizes") == sizes, "Live local catalogue sizes differ")
        output["model"] = dict(columns=count, trace_columns=trace_count, upper_rows=len(b),
                               equal_rows=len(f), catalogue_sizes=sizes)

        # Establish the new mathematical row from literal actual cones before
        # the integral-model scan and weighted exact-certificate arithmetic.
        output["Y_at_most_one_H27_validation"] = validate_y_at_most_one_h27(
            traces, A, b, labels, geometry, wanted_sha == V6_SOURCE_SHA256, check_time)

        # Validate all coefficients, RHS values and bounds, not only weighted
        # rows. Hash a documented integral encoding of the entire rebuilt model.
        model_hash = hashlib.sha256()
        model_hash.update(json.dumps(dict(traces=list(traces), labels=primitive(labels),
                                         A_shape=A.shape, E_shape=E.shape),
                                     sort_keys=True, separators=(",", ":")).encode())
        arrays = ((A.indptr, "A indptr"), (A.indices, "A columns"), (A.data, "A coefficients"),
                  (b, "A RHS"), (E.indptr, "E indptr"), (E.indices, "E columns"),
                  (E.data, "E coefficients"), (f, "E RHS"), (bounds, "box bounds"))
        for array, name in arrays:
            flat = np.asarray(array).reshape(-1)
            model_hash.update((name + ":" + str(len(flat)) + "\n").encode())
            for first in range(0, len(flat), 131072):
                chunk = flat[first:first + 131072]
                require(bool(np.all(np.isfinite(chunk))), f"Nonfinite {name}")
                require(bool(np.all(chunk == np.floor(chunk))), f"Nonintegral {name}")
                require(bool(np.all(np.abs(chunk) <= 2**53)), f"Unsafe floating integer range in {name}")
                model_hash.update(chunk.astype("<i8").tobytes())
                check_time()
        integer_bounds = [(int(lo), int(hi)) for lo, hi in bounds]
        require(all(lo <= hi for lo, hi in integer_bounds), "Inconsistent boxes")
        output["integer_model_validation"] = "all entries, right sides, and finite box endpoints validated"
        output["model_sha256"] = model_hash.hexdigest()
        output["model_hash_encoding"] = "JSON header of traces/labels/shapes, then named flattened CSR arrays/RHS/boxes as little-endian signed int64"
        output["extra_actual_member_validation"] = validate_extra_member_rows(
            traces, bounds, A, b, labels, geometry, kwargs, extra_metadata, check_time)
        output["triangle_row_validation"] = validate_triangle_rows(
            traces, A, b, labels, geometry, kwargs, SUPPORTED_SOURCES[wanted_sha], check_time)
        output["h27_clique_row_validation"] = validate_h27_rows(
            clique_data, traces, A, b, labels, geometry, kwargs, check_time)
        output["marked_B4_validation"] = validate_b4_rows_and_pruning(
            traces, bounds, A, b, E, f, labels, sizes, geometry, kwargs,
            wanted_sha in B4_SOURCES, check_time)

        scale = integer(dual.get("scale"), "dual scale")
        require(scale > 0, "Certificate scale must be positive")
        require(dual.get("inequality_sign") == "nonnegative weights on A*x<=b" and
                dual.get("equality_sign") == "signed weights on E*x=f", "Certificate sign convention differs")

        def sparse(key, length, nonnegative, labelled):
            entries = dual.get(key)
            require(isinstance(entries, list), f"Missing sparse {key} weights")
            result = []
            seen = set()
            for entry in entries:
                require(isinstance(entry, list) and len(entry) == (3 if labelled else 2), f"Malformed {key} entry")
                index, weight = integer(entry[0], key + " index"), integer(entry[1], key + " weight")
                require(0 <= index < length and index not in seen, f"Invalid or duplicate {key} index")
                require(weight != 0 and (not nonnegative or weight > 0), f"Invalid sparse {key} weight sign")
                if labelled:
                    require(entry[2] == primitive(labels[index]), f"Upper-row label mismatch at {index}")
                result.append((index, weight))
                seen.add(index)
            return result

        aw, ew = sparse("ineq", len(b), True, True), sparse("eq", len(f), False, False)
        q, H = [0] * count, 0
        for matrix, rhs, weights in ((A, b, aw), (E, f, ew)):
            for index, weight in weights:
                H += weight * int(rhs[index])
                for pos in range(matrix.indptr[index], matrix.indptr[index + 1]):
                    q[int(matrix.indices[pos])] += weight * int(matrix.data[pos])
                check_time()
        correction = 0
        q_hash = hashlib.sha256()
        for j, ((lo, hi), value) in enumerate(zip(integer_bounds, q)):
            objective_weight = 0 if zero or j >= trace_count else scale
            deficit = objective_weight - value
            correction += max(lo * deficit, hi * deficit)
            q_hash.update((str(value) + "\n").encode())
            if j % 16384 == 0:
                check_time()
        numerator = H + correction
        threshold = 0 if zero else 51 * scale
        strict = numerator < threshold
        for key, value in (("H", H), ("correction", correction), ("upper_numerator", numerator)):
            require(integer(dual.get(key), key) == value, f"Stored exact {key} disagrees")
        sign_key = "below0" if zero else "below51"
        require(type(dual.get(sign_key)) is bool and dual[sign_key] == strict,
                f"Stored {sign_key} sign disagrees with exact arithmetic")
        divisor = math.gcd(numerator, scale)
        output["exact_replay"] = dict(scale=scale, H=H, correction=correction,
                                       upper_numerator=numerator, target_numerator=threshold,
                                       strict_exclusion=strict, reduced_upper=[numerator // divisor, scale // divisor],
                                       q_columns=count, q_sha256_decimal_lines=q_hash.hexdigest(),
                                       nonzero_inequality_weights=len(aw), nonzero_equality_weights=len(ew),
                                       numerical_display="not used or trusted")
        if zero:
            output["exact_replay"].update(box_minimum=-correction, G=numerator,
                                          all_objective_coefficients_zero=True)
        for path, expected in tracked_files.items():
            require(sha(path) == expected, f"Bound input changed during replay: {path}")
        require(sha(__file__) == output["replayer_sha256"], "Replayer source changed during execution")
        check_time()
        output["all_inputs_unchanged"] = True
        output["result"] = "PASS"
        output["conclusion"] = (("Exact zero-objective box contradiction excludes the stated conditional model."
                                 if zero else "Exact trace upper bound excludes 51 residuals in the stated conditional model.")
                                if strict else "Exact arithmetic matches; these weights do not exclude the target.")
        return output
    except ReplayTimeout as exc:
        output.update(result="TIMEOUT", error=str(exc))
        return output
    except Exception as exc:
        output.update(result="FAIL", error=f"{type(exc).__name__}: {exc}")
        return output
    finally:
        for module, name, function in solver_restore:
            setattr(module, name, function)
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, previous_handler)
        if previous_timer[0] > 0:
            signal.setitimer(signal.ITIMER_REAL, max(0.001, previous_timer[0] - (time.monotonic() - started)),
                            previous_timer[1])
        output["seconds"] = time.monotonic() - started


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", required=True, type=Path)
    parser.add_argument("--source", default="auto", help="auto, current, or a supported pinned version v2/v3/v4/v5/v6")
    parser.add_argument("--seconds", type=float, default=30)
    args = parser.parse_args()
    if not math.isfinite(args.seconds) or not 0 < args.seconds <= 30:
        parser.error("--seconds must be positive and at most 30")
    if args.source not in ("auto", "current") and not re.fullmatch(r"v[1-9][0-9]*", args.source):
        parser.error("--source must be auto, current, or v followed by a positive integer")
    receipt = args.receipt.resolve()
    if not receipt.is_file():
        parser.error("--receipt must be an existing file")
    destination = HERE / "degree17_full_replay" / (receipt.stem + "-replay.json")
    if destination.exists():
        parser.error(f"Refusing to overwrite an existing replay: {destination}")
    result = replay(receipt, args.seconds, args.source)
    destination.parent.mkdir(exist_ok=True)
    with destination.open("x") as handle:
        json.dump(result, handle, indent=2, allow_nan=False)
        handle.write("\n")
    exact = result.get("exact_replay", {})
    print(json.dumps(dict(result=result["result"], receipt=str(receipt), output=str(destination),
                          certificate_kind=result.get("certificate_kind"),
                          strict_exclusion=exact.get("strict_exclusion"),
                          upper_numerator=exact.get("upper_numerator"),
                          seconds=result["seconds"], error=result.get("error"))), flush=True)
    return 0 if result["result"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
