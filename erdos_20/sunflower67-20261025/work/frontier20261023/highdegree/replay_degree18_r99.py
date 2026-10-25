#!/usr/bin/env python3
"""Replay one D18 R99 integer certificate without invoking a solver.

Uses the original hash-matched projection builder. This is shared-model exact
arithmetic replay, not independent model reconstruction, verification of the
geometric premises, Lean replay, or final review. Both status-0 upper-bound
receipts and the v3 phase-one receipt format are supported.

Example, when scheduled:
  python3 replay_degree18_r99.py --receipt degree18_r99/I01-none.json

Only one receipt is accepted. Imports, rebuilding, validation, and arithmetic
share a deadline of at most thirty seconds. No solver function is called.
"""

import argparse
import hashlib
import importlib.util
import inspect
import json
import math
from pathlib import Path
import signal
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


class ReplayError(ValueError):
    pass


class ReplayTimeout(TimeoutError):
    pass


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ReplayError(message)


def json_int(value, name):
    require(type(value) is int, f"{name} must be a JSON integer")
    return value


def primitive(value):
    return json.loads(json.dumps(value))


def equal_labels(model):
    from itertools import combinations

    labels = []
    for triple in model.LINK:
        points = [v for v in range(12) if triple >> v & 1]
        features = [model.mask(pair) for pair in combinations(points, 2)]
        features += [triple] + [1 << v for v in points]
        labels.append(["local-normalization", triple])
        labels.extend(["local-feature", triple, feature] for feature in features)
    return labels


def replay(receipt_path, seconds):
    start = time.monotonic()
    deadline = start + seconds
    output = {
        "result": "STARTED",
        "assurance": "shared-producer model reconstruction and exact integer certificate replay only; premises not re-proved; no solver, no Lean, no final review",
        "receipt_path": str(receipt_path),
        "receipt_sha256": sha(receipt_path),
        "replayer_sha256": sha(__file__),
        "compute_limit_seconds": seconds,
    }

    def check_time():
        if time.monotonic() >= deadline:
            raise ReplayTimeout("The per-case replay deadline expired")

    def alarm_handler(_signum, _frame):
        raise ReplayTimeout("The per-case replay deadline expired")

    def no_solver(*_args, **_kwargs):
        raise ReplayError("Solver invocation is forbidden during exact replay")

    previous = signal.signal(signal.SIGALRM, alarm_handler)
    signal.setitimer(signal.ITIMER_REAL, max(0.001, deadline - time.monotonic()))
    try:
        receipt = json.loads(receipt_path.read_text())
        phase = "phase_one_status" in receipt
        require(not phase, "This R99 replay supports exact upper-bound receipts only")
        output["receipt_kind"] = "phase-one-v3" if phase else "upper-bound"
        if phase:
            require("weights" in receipt and "exact_check" in receipt,
                    "Unsupported incomplete phase-one receipt: weights and exact_check are required")
            wanted_sha = receipt.get("rebuilt_source_sha256")
            local_sha = receipt.get("source_dependencies", {}).get("imported_local43_sha256")
            premises = receipt.get("original_premise_metadata", {})
        else:
            require(receipt.get("status") == 0 and "dual" in receipt,
                    "An ordinary receipt must have status 0 and a stored dual")
            wanted_sha = receipt.get("source_sha256")
            local_sha = receipt.get("imported_local43_sha256")
            premises = {key: receipt.get(key) for key in ("target_residuals", "mu", "point_cap", "assurance")}
        require(isinstance(wanted_sha, str) and len(wanted_sha) == 64,
                "Receipt does not specify a complete projection source SHA256")
        candidates = [HERE / f"degree18_r99_projection_v{v}.py" for v in range(1, 4)]
        candidates.append(HERE / "degree18_r99_projection.py")
        matches = [path for path in candidates if path.is_file() and sha(path) == wanted_sha]
        require(bool(matches), "No supported projection file exactly matches the receipt source hash")
        if phase:
            matches = [path for path in matches if path.name == "degree18_r99_projection_v3.py"]
            require(bool(matches), "Phase-one replay supports only the specified frozen v3 projection")
        source = matches[0]
        source_bytes = source.read_bytes()
        require(hashlib.sha256(source_bytes).hexdigest() == wanted_sha,
                "Projection source changed while selecting it")
        output["source"] = {
            "path": str(source), "sha256": wanted_sha, "source_match": True,
            "matching_paths": [str(path) for path in matches],
            "reconstruction": "same producer build(), never run()",
        }

        # Execute exactly the bytes just hashed, with __name__ different from
        # __main__. The producer's CLI and numerical run() are never entered.
        spec = importlib.util.spec_from_file_location("degree18_r99_replay_model", source)
        require(spec is not None, "Cannot create projection module specification")
        model = importlib.util.module_from_spec(spec)
        exec(compile(source_bytes, str(source), "exec"), model.__dict__)
        model.linprog = no_solver
        import numpy as np

        actual_local_path = Path(model.L.__file__).resolve()
        actual_local_sha = sha(actual_local_path)
        require(isinstance(local_sha, str) and actual_local_sha == local_sha,
                "Imported local43 source hash does not match the receipt")
        output["dependencies"] = {
            "local43_path": str(actual_local_path), "local43_sha256": actual_local_sha,
            "local43_source_match": True,
            "marker_catalogue": "Generated literally by the exact hashed model; separate coverage check required",
        }
        target = json_int(premises.get("target_residuals"), "target_residuals")
        require(target == 50, "This replayer is scoped to the target of 50 residuals")
        require(premises.get("mu") == 41 and premises.get("point_cap") == 18,
                "Receipt premise metadata must specify mu=41 and point_cap=18")
        case, empty = receipt["case"], receipt.get("empty", "none")
        assigned, forbidden = receipt.get("assigned"), receipt.get("forbidden", [])
        require(case in model.MARKERS, "Unknown marker case in the matched source")
        require(empty in ("none", "Y", "Z", "both"), "Invalid empty-component option")
        require(assigned is None or isinstance(assigned, dict) and not set(assigned) - {"Y", "Z"},
                "Assignments must use only components Y and Z")
        output["target_residuals"] = target
        output["literal_premises"] = {
            "receipt_metadata": premises,
            "case": case, "empty": empty, "assigned": assigned, "forbidden": forbidden,
            "fixed_link": "complete degree-18 P9 plus P9 link in the matched producer",
            "conditional_inputs": [
                "the source's universal incidence and exact-trace capacities and H27 disjoint-class bounds",
                "mu at least 41, point degrees at most 18, and the source's actual-anchor pair-degree-sum constraints",
                "the matched local43 and projection high-link, C5/P5, internal-cost, and catalogue filters",
                "the stated marker, component assignments, emptiness, and forbidden-trace assumptions",
            ],
            "status": "Literal imported model premises are recorded, not independently proved or transported from a set family here.",
        }
        parameters = inspect.signature(model.build).parameters
        kwargs = {"case": case, "empty": empty, "assigned": assigned}
        if "forbidden" in parameters:
            kwargs["forbidden"] = forbidden
        else:
            require(not forbidden, "This older matched builder does not support forbidden traces")
        check_time()
        traces, bounds, A, b, E, f, labels, sizes = model.build(**kwargs)
        A, E = A.tocsr(), E.tocsr()
        count = len(bounds)
        require(A.shape == (len(b), count) and E.shape == (len(f), count), "Model matrix shape mismatch")
        require(len(labels) == len(b), "Inequality label count mismatch")
        stored_count = receipt.get("model", {}).get("original_columns") if phase else receipt.get("columns")
        require(stored_count == count, "Rebuilt column count differs from the receipt")
        output["model"] = {
            "trace_columns": len(traces), "original_columns": count,
            "inequality_rows": len(b), "equality_rows": len(f), "catalogue_sizes": sizes,
        }

        # Validate every original coefficient, RHS, and bound, including rows
        # receiving weight zero. Numpy only checks the stored integral arrays;
        # all weighted sums and box computations below use Python integers.
        def validate_integral(array, name):
            flat = np.asarray(array).reshape(-1)
            for first in range(0, len(flat), 262144):
                chunk = flat[first:first + 262144]
                require(bool(np.all(np.isfinite(chunk))), f"Nonfinite {name}")
                require(bool(np.all(chunk == np.floor(chunk))), f"Nonintegral {name}")
                check_time()

        for array, name in ((A.data, "A coefficients"), (E.data, "E coefficients"),
                            (b, "b RHS"), (f, "f RHS"), (bounds, "box bounds")):
            validate_integral(array, name)
        integer_bounds = [(int(lo), int(hi)) for lo, hi in bounds]
        require(all(lo <= hi for lo, hi in integer_bounds), "Inconsistent original box bounds")
        output["integer_model_validation"] = "all stored coefficients, RHS values, and box bounds are finite integers"

        if phase:
            weights = receipt["weights"]
            scale = json_int(receipt.get("scale"), "scale")
            require(scale == 10**10, "Unexpected phase-one rounding scale")
            def dense(key, length, nonnegative):
                vector = weights.get(key)
                require(isinstance(vector, list) and len(vector) == length, f"Invalid {key} weight length")
                for index, value in enumerate(vector):
                    json_int(value, f"{key}[{index}]")
                    require(not nonnegative or value >= 0, f"Negative {key} weight")
                return vector
            aw = dense("inequality", len(b), True)
            ep = dense("equality_positive", len(f), True)
            en = dense("equality_negative", len(f), True)
            ew = [positive - negative for positive, negative in zip(ep, en)]
            require(dense("equality_signed", len(f), False) == ew, "Signed equality weight mismatch")
            require(weights.get("inequality_labels") == primitive(labels), "Inequality label metadata mismatch")
            require(weights.get("equality_labels") == equal_labels(model), "Equality label/sign ordering mismatch")
            require(weights.get("slack_column_coefficient") == -sum(aw) - sum(ep) - sum(en),
                    "Phase-one slack sign metadata mismatch")
            formulation = receipt.get("phase_one_formulation", {})
            require(formulation.get("equality_positive_sign") == 1 and formulation.get("equality_negative_sign") == -1,
                    "Phase-one equality sign metadata is missing or inconsistent")
        else:
            dual = receipt["dual"]
            scale = json_int(dual.get("scale"), "dual scale")
            require(scale > 0, "Dual scale must be positive")
            def sparse(key, length, nonnegative, labelled):
                entries = dual.get(key)
                require(isinstance(entries, list), f"Missing sparse {key} weights")
                vector = [0] * length
                seen = set()
                for entry in entries:
                    require(isinstance(entry, list) and len(entry) == (3 if labelled else 2), f"Malformed {key} entry")
                    index = json_int(entry[0], f"{key} row index")
                    weight = json_int(entry[1], f"{key} weight")
                    require(0 <= index < length and index not in seen, f"Invalid or repeated {key} index {index}")
                    require(not nonnegative or weight >= 0, "Negative inequality multiplier")
                    if labelled:
                        require(entry[2] == primitive(labels[index]), f"Inequality label mismatch at {index}")
                    seen.add(index)
                    vector[index] = weight
                return vector
            aw = sparse("ineq", len(b), True, True)
            ew = sparse("eq", len(f), False, False)

        q = [0] * count
        H = 0
        for matrix, rhs, vector in ((A, b, aw), (E, f, ew)):
            for i, weight in enumerate(vector):
                if weight:
                    H += weight * int(rhs[i])
                    for k in range(matrix.indptr[i], matrix.indptr[i + 1]):
                        q[int(matrix.indices[k])] += weight * int(matrix.data[k])
                if i % 32 == 0:
                    check_time()
        q_hash = hashlib.sha256()
        for value in q:
            q_hash.update((str(value) + "\n").encode())
        exact = {"scale": scale, "H": H, "q_column_count": count,
                 "q_sha256_decimal_lines": q_hash.hexdigest(),
                 "inequality_weights_nonnegative": all(weight >= 0 for weight in aw)}
        if phase:
            box_minimum = sum(min(lo * value, hi * value) for (lo, hi), value in zip(integer_bounds, q))
            gap = H - box_minimum
            stored = receipt["exact_check"]
            for key, value in (("H", H), ("box_minimum", box_minimum), ("G", gap), ("q_column_count", count)):
                require(json_int(stored.get(key), key) == value, f"Stored phase-one {key} disagrees")
            require(stored.get("q_sha256_decimal_lines") == q_hash.hexdigest(), "Stored phase-one q digest disagrees")
            require(type(stored.get("strict_negative_gap")) is bool and stored["strict_negative_gap"] == (gap < 0),
                    "Stored phase-one gap sign disagrees")
            require(stored.get("all_source_row_weights_nonnegative") is True, "Stored source-row sign check disagrees")
            exact.update(box_minimum=box_minimum, G=gap, strict_negative_gap=gap < 0)
            conclusion = "Rebuilt conditional model has an exact box contradiction." if gap < 0 else "Exact arithmetic matches, but these weights do not contradict the model."
        else:
            correction = 0
            for j, ((lo, hi), value) in enumerate(zip(integer_bounds, q)):
                deficit = (scale if j < len(traces) else 0) - value
                correction += max(lo * deficit, hi * deficit)
            numerator = H + correction
            below = numerator < target * scale
            for key, value in (("H", H), ("correction", correction), ("upper_numerator", numerator)):
                require(json_int(dual.get(key), key) == value, f"Stored upper-bound {key} disagrees")
            require(type(dual.get("below50")) is bool and dual["below50"] == below,
                    "Stored below50 comparison disagrees")
            divisor = math.gcd(numerator, scale)
            exact.update(correction=correction, upper_numerator=numerator,
                         reduced_upper=[numerator // divisor, scale // divisor],
                         target_numerator=target * scale, below_target=below,
                         numerical_display="not used or trusted")
            conclusion = "Exact conditional bound excludes 50 residuals." if below else "Exact bound matches but does not exclude 50 residuals."
        check_time()
        output["exact_replay"] = exact
        output["conclusion"] = conclusion
        output["result"] = "PASS"
        return output
    except ReplayTimeout as exc:
        output.update(result="TIMEOUT", error=str(exc))
        return output
    except Exception as exc:
        output.update(result="FAIL", error=f"{type(exc).__name__}: {exc}")
        return output
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, previous)
        output["seconds"] = time.monotonic() - start


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", required=True, type=Path)
    parser.add_argument("--seconds", type=float, default=30)
    args = parser.parse_args()
    if not 0 < args.seconds <= 30:
        parser.error("--seconds must be positive and at most 30")
    path = args.receipt.resolve()
    if not path.is_file():
        parser.error("--receipt must identify an existing file")
    result = replay(path, args.seconds)
    destination = HERE / "degree18_r99" / (path.stem + "-replay.json")
    destination.parent.mkdir(exist_ok=True)
    temporary = destination.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(result, indent=2, allow_nan=False) + "\n")
    temporary.replace(destination)
    print(json.dumps({"result": result["result"], "receipt": str(path),
                      "output": str(destination), "seconds": result["seconds"],
                      "conclusion": result.get("conclusion"), "error": result.get("error")}), flush=True)
    return 0 if result["result"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
