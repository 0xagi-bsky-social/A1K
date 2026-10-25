#!/usr/bin/env python3
"""Replay one D18 component phase-one certificate using Python integers only.

Select degree18_component_v1.py or degree18_component.py by the receipt's exact
source SHA256. Rebuild with build(), never run() or matrix(); no solver or SciPy
is used. The per-case deadline includes source loading, the small internal
catalogue, local necessary-state construction, validation, and exact arithmetic.
This is shared-producer model reconstruction, not independent geometry or Lean.
"""

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import signal
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


class ReplayError(ValueError):
    pass


class ReplayTimeout(TimeoutError):
    pass


def require(condition, message):
    if not condition:
        raise ReplayError(message)


def integer(value, name):
    require(type(value) is int, f"{name} must be an integer, not a boolean or float")
    return value


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def canonical_hash(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"),
                                     allow_nan=False).encode()).hexdigest()


def replay(receipt_path, seconds=20, source_choice="auto"):
    started = time.monotonic()
    output = {
        "result": "STARTED",
        "assurance": "certificate-diagnostic: shared-producer model reconstruction and exact integer replay; no solver, no Lean, no independent model proof",
        "receipt_path": str(receipt_path),
        "replayer_sha256": sha(__file__),
        "compute_limit_seconds": seconds,
    }

    def timeout_handler(_signum, _frame):
        raise ReplayTimeout("The per-case 20-second-or-less deadline expired")

    def check_time():
        if time.monotonic() - started >= seconds:
            raise ReplayTimeout("The per-case deadline expired")

    def forbidden_call(*_args, **_kwargs):
        raise ReplayError("Numerical producer/matrix invocation is forbidden during replay")

    previous = signal.signal(signal.SIGALRM, timeout_handler)
    signal.setitimer(signal.ITIMER_REAL, seconds)
    try:
        receipt_bytes = receipt_path.read_bytes()
        output["receipt_sha256"] = hashlib.sha256(receipt_bytes).hexdigest()
        receipt = json.loads(receipt_bytes)
        require(integer(receipt.get("status"), "status") == 0,
                "Receipt must contain a completed phase-one solve and its certificate")
        cert = receipt.get("certificate")
        require(isinstance(cert, dict), "Missing phase-one certificate")
        wanted_sha = receipt.get("source_sha256")
        require(isinstance(wanted_sha, str) and re.fullmatch(r"[0-9a-f]{64}", wanted_sha),
                "Invalid projection source SHA256")
        candidates = {
            "v1": HERE / "degree18_component_v1.py",
            "current": HERE / "degree18_component.py",
        }
        choices = candidates.items() if source_choice == "auto" else [(source_choice, candidates[source_choice])]
        matches = [(name, path) for name, path in choices if path.is_file() and sha(path) == wanted_sha]
        require(bool(matches), "No selected supported source matches the receipt SHA256")
        source_name, source = matches[0]
        source_bytes = source.read_bytes()
        require(hashlib.sha256(source_bytes).hexdigest() == wanted_sha,
                "Source changed during selection")
        output["source"] = {"name": source_name, "path": str(source), "sha256": wanted_sha,
                            "matching_names": [name for name, _ in matches]}
        spec = importlib.util.spec_from_file_location("component18_replay_model", source)
        require(spec is not None, "Cannot create model import specification")
        model = importlib.util.module_from_spec(spec)
        exec(compile(source_bytes, str(source), "exec"), model.__dict__)
        # Neither entry point is needed by a replay. Fail closed if later code
        # accidentally attempts to invoke either producer entry point.
        model.run = forbidden_call
        model.matrix = forbidden_call
        local_path = Path(model.L.__file__).resolve()
        local_sha = sha(local_path)
        require(local_sha == receipt.get("local43_sha256"), "local43 hash differs from receipt")
        output["local43"] = {"path": str(local_path), "sha256": local_sha, "match": True}

        case = receipt.get("case")
        require(isinstance(case, dict) and set(case) ==
                {"id", "component", "outside", "r10", "r9", "interiors"}, "Invalid case fields")
        component = integer(case["component"], "component")
        require(component in (9, 10), "Only P9 and P10 components are supported")
        require(integer(case["outside"], "outside") == 18 - component,
                "Outside link component size must complete degree 18")
        require(integer(case["r10"], "r10") == 0 and integer(case["r9"], "r9") == 0,
                "Only bootstrap-free r10=r9=0 is supported")
        require(isinstance(case["id"], str) and re.fullmatch(f"P{component}_[0-9]{{3}}", case["id"]),
                "Invalid case identifier")
        require(isinstance(case["interiors"], list), "Interior assignment must be a list")
        for i, quad in enumerate(case["interiors"]):
            require(isinstance(quad, list) and len(quad) == 4, f"Interior {i} is not a four-set")
            for vertex in quad:
                require(0 <= integer(vertex, "interior vertex") < 6, "Interior vertex outside support")
            require(quad == sorted(set(quad)), "Interior must have four distinct sorted vertices")
        catalogue = model.catalog(component)
        records = [record for record in catalogue["records"] if record["id"] == case["id"]]
        require(len(records) == 1 and records[0]["interiors"] == case["interiors"],
                "Case does not match its complete internal-orbit representative")
        output["case"] = case
        output["catalogue"] = {
            "internal_count": catalogue["internal_count"],
            "automorphism_count": catalogue["automorphism_count"],
            "orbit_count": len(catalogue["records"]),
            "orbit_size": records[0]["orbit_size"],
            "sha256": canonical_hash(catalogue),
            "coverage": "producer recursion checks equality of generated and orbit-covered assignments",
        }
        output["literal_premises"] = {
            "family": "finite simple SF4, empty-core sunflowers forbidden, cardinality at least 68",
            "global_degree_cap": 18, "minimum_closed_neighborhood": 41,
            "complete_centre_link": f"P{component} plus a disjoint-support intersecting family of {18-component} triples",
            "component_support": "six specified points; arbitrary exterior identities and multiplicities",
            "internal_assignment": "exactly case.interiors",
            "bootstrap": {"r10": 0, "r9": 0},
            "imported": "H27; universal SF2/SF3 capacities, I8/I9/I10, isolation, B4, R16/high-link structure, trace margins, C5 confinement, pair/singleton resources",
            "boundary": "Rows are interpreted separately in D18-P10-internals.md; this replay does not prove their geometry.",
        }
        check_time()
        data = model.build(case)
        require(data["case"] == case, "Builder changed case metadata")
        bounds = data["bounds"]
        require(isinstance(bounds, list), "Bounds must be a finite list")
        n = len(bounds)
        for j, bound in enumerate(bounds):
            require(isinstance(bound, (list, tuple)) and len(bound) == 2, f"Malformed box {j}")
            lo, hi = [integer(value, f"box {j}") for value in bound]
            require(lo <= hi, f"Inconsistent box {j}")
        upper, equal = data["upper"], data["equal"]
        require(integer(receipt.get("columns"), "columns") == n, "Column count mismatch")
        require(integer(receipt.get("upper_rows"), "upper_rows") == len(upper), "Upper row count mismatch")
        require(integer(receipt.get("equal_rows"), "equal_rows") == len(equal), "Equal row count mismatch")
        require(receipt.get("live_sizes") == data["live_sizes"], "Local catalogue sizes differ")
        require(len(data["quads"]) == 41 and tuple(data["quads"]) == tuple(model.U),
                "Expected the 41 proper nonempty component-trace coordinates")
        require(integer(data["target"], "target") == 0 and
                len(data["objective"]) == n and
                all(integer(value, "objective coefficient") == 0 for value in data["objective"]),
                "Unexpected original objective")
        packed = []
        for group, rows in (("upper", upper), ("equal", equal)):
            for i, row in enumerate(rows):
                require(isinstance(row, (tuple, list)) and len(row) == 3, f"Malformed {group} row {i}")
                name, terms, rhs = row
                require(isinstance(name, str) and isinstance(terms, dict), f"Invalid {group} row representation")
                integer(rhs, f"{group} RHS {i}")
                for j, value in terms.items():
                    require(0 <= integer(j, "column index") < n, "Column index out of bounds")
                    integer(value, f"{group} coefficient {i}:{j}")
                packed.append([group, name, sorted(terms.items()), rhs])
                if i % 64 == 0:
                    check_time()
        output["model"] = {
            "columns": n, "trace_columns": 41, "upper_rows": len(upper), "equal_rows": len(equal),
            "live_sizes": data["live_sizes"], "internal_degrees": data["internal_degrees"],
            "degree_caps": data["caps"], "zero_trace_indices": sorted(data["zero"]),
            "sha256": canonical_hash({"bounds": bounds, "rows": packed}),
            "all_coefficients_rhs_and_bounds": "validated Python integers, including zero-weight rows",
        }

        scale = integer(cert.get("scale"), "scale")
        require(scale == 10**10, "Unexpected recorded phase-one scale")
        total = len(upper) + 2 * len(equal)
        weights = cert.get("weights")
        require(isinstance(weights, list), "Missing sparse weights")
        q = [0] * n
        H = 0
        seen = set()
        used_rows = []
        for entry in weights:
            require(isinstance(entry, list) and len(entry) == 2, "Malformed sparse weight")
            i, weight = integer(entry[0], "weight index"), integer(entry[1], "weight")
            require(0 <= i < total and i not in seen, "Invalid or duplicate weight index")
            require(weight > 0, "Sparse source-row weights must be strictly positive")
            seen.add(i)
            if i < len(upper):
                row, sign, group, local_index = upper[i], 1, "A", i
            elif i < len(upper) + len(equal):
                local_index = i - len(upper)
                row, sign, group = equal[local_index], 1, "E"
            else:
                local_index = i - len(upper) - len(equal)
                row, sign, group = equal[local_index], -1, "-E"
            name, terms, rhs = row
            H += weight * sign * rhs
            for j, value in terms.items():
                q[j] += weight * sign * value
            used_rows.append([i, weight, group, local_index, name])
        minimum = sum(min(lo * value, hi * value) for (lo, hi), value in zip(bounds, q))
        gap = H - minimum
        for key, value in (("H", H), ("minimum", minimum), ("G", gap)):
            require(integer(cert.get(key), f"stored {key}") == value, f"Stored {key} disagrees with replay")
        require(type(cert.get("negative")) is bool and cert["negative"] == (gap < 0),
                "Stored negative-gap flag disagrees")
        output["exact"] = {
            "scale": scale, "H": H, "minimum": minimum, "G": gap, "negative": gap < 0,
            "q_sha256_decimal_lines": hashlib.sha256("".join(f"{v}\n" for v in q).encode()).hexdigest(),
            "q_column_count": n, "source_weights_nonnegative": True,
            "weighted_rows": used_rows, "assembled_order": ["A", "E", "-E"],
            "formula": "G = H - sum_j min(l_j*q_j, u_j*q_j), every original column, no artificial slack column",
        }
        require(source.read_bytes() == source_bytes and sha(local_path) == local_sha,
                "Source dependency changed during replay")
        require(receipt_path.read_bytes() == receipt_bytes, "Input receipt changed during replay")
        check_time()
        output["result"] = "PASS" if gap < 0 else "MATCH_NONNEGATIVE"
        output["conclusion"] = ("The hash-matched conditional model is exactly infeasible."
                                if gap < 0 else "Arithmetic matches; no infeasibility follows from these weights.")
    except ReplayTimeout as exc:
        output.update(result="TIMEOUT", error=str(exc))
    except Exception as exc:
        output.update(result="FAIL", error=f"{type(exc).__name__}: {exc}")
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, previous)
        output["elapsed_seconds"] = time.monotonic() - started
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path, required=True)
    parser.add_argument("--source", choices=("auto", "v1", "current"), default="auto")
    parser.add_argument("--seconds", type=float, default=20)
    args = parser.parse_args()
    if not 0 < args.seconds <= 20:
        parser.error("--seconds must be positive and at most 20")
    receipt_path = args.receipt.resolve()
    if not receipt_path.is_file():
        parser.error("--receipt must be an existing file")
    record = replay(receipt_path, args.seconds, args.source)
    output = HERE / "degree18-replay" / (receipt_path.stem + "-replay.json")
    output.parent.mkdir(exist_ok=True)
    temporary = output.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(record, indent=2, allow_nan=False) + "\n")
    temporary.replace(output)
    print(json.dumps({"case": record.get("case", {}).get("id", receipt_path.stem),
                      "result": record["result"], "G": record.get("exact", {}).get("G"),
                      "columns": record.get("model", {}).get("columns"),
                      "seconds": round(record["elapsed_seconds"], 4),
                      **({"error": record["error"]} if "error" in record else {})},
                     separators=(",", ":")), flush=True)
    return 0 if record["result"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
