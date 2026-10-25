#!/usr/bin/env python3
"""Replay one hash-bound P10+I8 integer-box certificate without a solver.

Supports trace-objective upper bounds (<50) and explicitly tagged zero-objective
infeasibility certificates (<0), using their unchanged hash-matched producer
build(). Frozen v2/v3 and later compatible versions are selected by SHA256, never
by assuming that the current source equals the receipt source. Geometry, literal
premises, dependency files, complete boxes, and every matrix entry are checked.

This is shared-producer model reconstruction and exact arithmetic replay. It is
not independent model reconstruction, a proof of imported mathematical premises,
Lean verification, or a complete branch proof. One case only, at most 30 seconds.
"""

import argparse
import hashlib
import importlib.util
import inspect
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
    frozen = sorted(HERE.glob("degree18_p10_projection_v*.py"),
                    key=lambda p: int(re.search(r"_v([0-9]+)\.py$", p.name).group(1))
                    if re.search(r"_v([0-9]+)\.py$", p.name) else -1)
    frozen = [p for p in frozen if re.search(r"_v[0-9]+\.py$", p.name)]
    current = HERE / "degree18_p10_projection.py"
    if choice == "auto":
        return frozen + [current]
    if choice == "current":
        return [current]
    require(bool(re.fullmatch(r"v[1-9][0-9]*", choice)), "Invalid --source selector")
    return [HERE / f"degree18_p10_projection_{choice}.py"]


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
            output["certificate_producer"] = bind_file(
                HERE / "degree18_p10_phaseone.py", receipt.get("certificate_producer_sha256"),
                "phase-one producer")
            output["original_metadata_preserved"] = True
        else:
            require(dual.get("objective", "trace") == "trace",
                    "Trace upper certificate has a conflicting objective tag")
            require("original_status" not in receipt and "below0" not in dual,
                    "Untagged phase-one metadata cannot be replayed as a trace objective")
        output["certificate_kind"] = certificate_kind
        output["objective"] = "all-zero" if zero else "one on trace columns, zero on selectors"

        wanted_sha = digest_string(receipt.get("source_sha256"), "projection source")
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
        spec = importlib.util.spec_from_file_location("degree18_p10_exact_replay_model", source)
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

        require(integer(receipt.get("target_residuals"), "target_residuals") == 50,
                "Receipt must have residual target 50")
        require(integer(receipt.get("mu"), "mu") == 41 and
                integer(receipt.get("point_cap"), "point_cap") == 18,
                "Receipt must state mu41 and global point cap18")
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
        require(set(inspect.signature(model.build).parameters) == set(CASE_KEYS),
                "This producer has an unsupported build signature; update the explicit replay adapter")
        require(kwargs["case"] in model.marker_catalogue(kwargs["kind"]), "Unknown marker case")
        actual_premises = primitive(model.premises(**kwargs))
        require(receipt.get("literal_premises") == actual_premises, "Literal mathematical premises differ from producer")
        geometry = primitive(model.catalogue_metadata(kwargs["kind"]))
        require(receipt.get("geometry") == geometry, "Complete component/marker geometry differs from receipt")
        output["case"] = kwargs
        output["literal_premises"] = actual_premises
        output["geometry_sha256"] = digest_value(geometry)
        output["geometry_validation"] = "complete producer catalogue reproduced, including its exhaustive group/orbit coverage checks"

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
        output["dependencies"] = dependencies
        identity = dict(source_sha256=wanted_sha,
                        imported_local43_sha256=receipt["imported_local43_sha256"],
                        structural_note_sha256=receipt["structural_note_sha256"],
                        pool_note_sha256=receipt["pool_note_sha256"],
                        imported_crowding_sources=recorded_imports,
                        kind=kwargs["kind"], literal_premises=actual_premises)
        premise_sha = digest_value(identity)
        require(digest_string(receipt.get("premise_sha256"), "premise identity") == premise_sha,
                "Stored premise fingerprint differs from rebuilt source/dependency/premise identity")
        output["premise_sha256"] = premise_sha

        check_time()
        traces, bounds, A, b, E, f, labels, sizes = model.build(**kwargs)
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
        threshold = 0 if zero else 50 * scale
        strict = numerator < threshold
        for key, value in (("H", H), ("correction", correction), ("upper_numerator", numerator)):
            require(integer(dual.get(key), key) == value, f"Stored exact {key} disagrees")
        sign_key = "below0" if zero else "below50"
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
                                 if zero else "Exact trace upper bound excludes 50 residuals in the stated conditional model.")
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
    parser.add_argument("--source", default="auto", help="auto, current, or a frozen version such as v2/v3")
    parser.add_argument("--seconds", type=float, default=30)
    args = parser.parse_args()
    if not math.isfinite(args.seconds) or not 0 < args.seconds <= 30:
        parser.error("--seconds must be positive and at most 30")
    if args.source not in ("auto", "current") and not re.fullmatch(r"v[1-9][0-9]*", args.source):
        parser.error("--source must be auto, current, or v followed by a positive integer")
    receipt = args.receipt.resolve()
    if not receipt.is_file():
        parser.error("--receipt must be an existing file")
    destination = HERE / "degree18_p10_replay" / (receipt.stem + "-replay.json")
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
