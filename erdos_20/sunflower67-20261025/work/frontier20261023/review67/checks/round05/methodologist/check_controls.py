"""Bounded controls: real early guards and extracted exact-arithmetic block only.

No numerical-package imports, model construction, solver, or leaf replay.
"""
import ast
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace

sys.dont_write_bytecode = True
BASE = Path(__file__).resolve().parents[3]
SOURCE = BASE.parent / "highdegree/replay_degree17_full_v9.py"
WRAPPER = BASE / "replay_d17_leaf_fresh.py"


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


replayer = load(SOURCE, "methodologist_replayer")
wrapper = load(WRAPPER, "methodologist_wrapper")
results = []
with tempfile.TemporaryDirectory(prefix="methodologist-r5-") as directory:
    root = Path(directory)
    receipt = root / "unsupported.json"
    receipt.write_text(json.dumps({"status": 0, "dual": {}, "source_sha256": "0" * 64}))
    result = replayer.replay(receipt, 2, "auto")
    assert result["result"] == "FAIL" and "Unsupported source SHA256" in result["error"]
    results.append({"check": "unsupported source digest", "observation": result["error"]})
    destination = root / "occupied.json"
    destination.write_text("sentinel")
    sys.argv = [str(WRAPPER), str(receipt), "--output", str(destination)]
    try:
        wrapper.main()
        raise AssertionError("existing output accepted")
    except FileExistsError:
        assert destination.read_text() == "sentinel"
        results.append({"check": "existing wrapper output", "observation": "FileExistsError; sentinel unchanged"})
    changed_source = root / "changed.py"
    changed_source.write_text("raise AssertionError('must not execute')\n")
    wrapper.REPLAYER = changed_source
    sys.argv = [str(WRAPPER), str(receipt), "--output", str(root / "fresh.json")]
    try:
        wrapper.main()
        raise AssertionError("changed evaluator accepted")
    except ValueError as exc:
        assert str(exc) == "Frozen replay evaluator changed"
        assert not (root / "fresh.json").exists()
        results.append({"check": "wrapper evaluator pin", "observation": str(exc)})

# Execute the unchanged arithmetic body from scale parsing through zero metadata.
# The enclosing numerical model construction and matrix scans are not executed.
tree = ast.parse(SOURCE.read_text())
replay_node = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == "replay")
try_node = next(n for n in replay_node.body if isinstance(n, ast.Try))
start = next(i for i, n in enumerate(try_node.body)
             if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "scale" for t in n.targets))
end = next(i for i, n in enumerate(try_node.body[start:], start)
           if isinstance(n, ast.For) and isinstance(n.target, ast.Tuple)
           and [x.id for x in n.target.elts if isinstance(x, ast.Name)] == ["path", "expected"])
body = copy.deepcopy(try_node.body[start:end])
body.append(ast.Return(value=ast.Name(id="output", ctx=ast.Load())))
arguments = "dual labels b f A E count trace_count integer_bounds zero output check_time".split()
function = ast.FunctionDef(name="arithmetic", args=ast.arguments(posonlyargs=[],
    args=[ast.arg(arg=a) for a in arguments], kwonlyargs=[], kw_defaults=[], defaults=[]),
    body=body, decorator_list=[])
module = ast.fix_missing_locations(ast.Module(body=[function], type_ignores=[]))
namespace = dict(replayer.__dict__)
exec(compile(module, str(SOURCE) + " [arithmetic block]", "exec"), namespace)
arithmetic = namespace["arithmetic"]


def matrix(rows):
    indices, data, indptr = [], [], [0]
    for row in rows:
        for j, value in enumerate(row):
            if value:
                indices.append(j)
                data.append(value)
        indptr.append(len(indices))
    return SimpleNamespace(indices=indices, data=data, indptr=indptr)


signs = {"scale": 1, "inequality_sign": "nonnegative weights on A*x<=b",
         "equality_sign": "signed weights on E*x=f"}
# x is the trace variable, y the selector, x<=51*y, boxes x in[0,51], y in[0,1].
# Exhaustive enumeration separately confirms a feasible target x=51.
dual = dict(signs, ineq=[[0, 1, "selector-coupling"]], eq=[], H=0,
            correction=51, upper_numerator=51, below51=False)
args = (dual, ["selector-coupling"], [0], [], matrix([[1, -51]]), matrix([]),
        2, 1, [(0, 51), (0, 1)], False, {}, lambda: None)
exact = arithmetic(*args)["exact_replay"]
maximum = max(x for x in range(52) for y in range(2) if x <= 51 * y)
assert maximum == exact["upper_numerator"] == 51
assert exact["q_columns"] == 2 and exact["strict_exclusion"] is False
results.append({"check": "selector correction and equality threshold",
                "observation": "All 104 integer box points enumerated: optimum51; correction51 includes selector; strict_exclusion=false."})
for label, patch in [("zero scale", {"scale": 0}),
                     ("omitted selector correction", {"correction": 0, "upper_numerator": 0, "below51": True}),
                     ("incorrect strict flag", {"below51": True}),
                     ("out-of-range sparse row", {"ineq": [[1, 1, "selector-coupling"]]}),
                     ("boolean sparse coefficient", {"ineq": [[0, True, "selector-coupling"]]})]:
    altered = dict(dual, **patch)
    try:
        arithmetic(altered, *args[1:])
        raise AssertionError(label + " accepted")
    except replayer.ReplayError as exc:
        results.append({"check": label, "observation": str(exc)})

zero_dual = dict(signs, ineq=[[0, 1, "impossible"]], eq=[], H=-1,
                 correction=0, upper_numerator=-1, below0=True)
zero = arithmetic(zero_dual, ["impossible"], [-1], [], matrix([[-1]]), matrix([]),
                  1, 1, [(0, 0)], True, {}, lambda: None)["exact_replay"]
assert zero["strict_exclusion"] is True and zero["all_objective_coefficients_zero"] is True
results.append({"check": "explicit zero objective", "observation": "Impossible x=0,-x<=-1 gives G=-1,target0 and strict_exclusion=true."})

output = {"scope": "Standard-library early guards plus extracted arithmetic block; no full model or replay",
          "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
          "wrapper_sha256": hashlib.sha256(WRAPPER.read_bytes()).hexdigest(),
          "checks": results, "result": "PASS"}
destination = Path(__file__).with_name("results.json")
with destination.open("x") as stream:
    json.dump(output, stream, indent=2)
    stream.write("\n")
print(json.dumps(output, indent=2))
