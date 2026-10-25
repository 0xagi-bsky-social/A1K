"""Small literal adversarial checks; no model, numerical library, or full replay."""
import ast
import hashlib
import itertools as it
import json
from pathlib import Path

BASE = Path(__file__).resolve().parents[3]
HIGH = BASE.parent / "highdegree"


def mask(points):
    return sum(1 << p for p in points)


def sunflower(a, b, c):
    return len({a, b, c}) == 3 and a & b == a & c == b & c


# Missing the actual marker's exterior point makes trace equality unsound.
t = frozenset((0, 1, 2))
cone = t | {13}
marker = frozenset((0, 6, 7, 12))
other = frozenset((0, 8, 9, 12))
old_core = frozenset(range(12))
assert (other & old_core) & t == (other & old_core) & (marker & old_core) == t & marker
assert not sunflower(cone, marker, other)
assert other & marker == {0, 12}
new_core = frozenset(range(13))
assert not ((other & new_core) & t == (other & new_core) & marker == t & marker)

# Independently compare the implemented bit predicate to actual intersections.
p10 = [frozenset(map(int, word)) for word in "012 015 023 034 045 124 134 135 235 245".split()]
link = p10 + [frozenset(v + 6 for v in q) for q in p10[1:]]
comparisons = 0
for k in range(5):
    for points in it.combinations(range(13), k):
        trace = frozenset(points)
        for fresh in (14, 18):
            actual = trace | frozenset(range(fresh, fresh + 4 - k))
            for block in link:
                code = mask(trace) & mask(block) == mask(trace) & mask(marker) == mask(block) & mask(marker)
                literal = sunflower(actual, marker, block | {13})
                assert code == literal
                comparisons += 1

# Run the unchanged forbidden-trace gate extracted from the actual stage source.
stage = HIGH / "check_d17_stage_plan_v9.py"
tree = ast.parse(stage.read_text())
check = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == "check")
loop = next(n for n in ast.walk(check) if isinstance(n, ast.For)
            and isinstance(n.iter, ast.Subscript) and isinstance(n.iter.value, ast.Name)
            and n.iter.value.id == "plan")
gate = next(n for n in loop.body if isinstance(n, ast.For)
            and isinstance(n.target, ast.Name) and n.target.id == "s"
            and isinstance(n.iter, ast.Name) and n.iter.id == "forbidden")
args = "forbidden core_mask prior_four prior_three nid".split()
fun = ast.FunctionDef(name="gate", args=ast.arguments(posonlyargs=[],
    args=[ast.arg(arg=a) for a in args], kwonlyargs=[], kw_defaults=[], defaults=[]),
    body=[gate], decorator_list=[])
compiled = ast.fix_missing_locations(ast.Module(body=[fun], type_ignores=[]))


def require(condition, message):
    if not condition:
        raise ValueError(message)


ns = {"require": require}
exec(compile(compiled, str(stage) + " [forbidden gate]", "exec"), ns)
three = mask((0, 6, 7))
four = three | (1 << 8)
try:
    ns["gate"]([three], (1 << 13) - 1, {four}, set(), "synthetic")
    raise AssertionError("An absent four-set wrongly justified a proper trace")
except ValueError as exc:
    absent_four_rejection = str(exc)
# A proved absent proper trace justifies each restriction lift, including the
# represented exterior marker. This is the permitted opposite direction.
ns["gate"]([three, three | (1 << 13)], (1 << 13) - 1, set(), {three}, "synthetic")

# Independently exhaust all small bipartite link graphs used in LOW14.
edges = [frozenset((a, b)) for a in range(3) for b in (3, 4)]
accepted = 0
for bits in range(1 << len(edges)):
    graph = [e for i, e in enumerate(edges) if bits >> i & 1]
    if len(graph) < 3 or max(sum(v in e for e in graph) for v in range(5)) > 2:
        continue
    disjoint = next((pair for pair in it.combinations(graph, 2) if not pair[0] & pair[1]), None)
    assert disjoint is not None
    # t=5, two Q8 hubs6,7 outside the near support; common root i=8.
    triples = [e | {5} for e in disjoint] + [frozenset((5, 6, 7))]
    assert sunflower(*triples)
    assert sunflower(*(tr | {8} for tr in triples))
    accepted += 1
triangle = [frozenset(e) for e in ((0, 1), (1, 2), (0, 2))]
star = [frozenset((0, v)) for v in (1, 2, 3)]
assert all(a & b for a, b in it.combinations(triangle, 2))
assert all(a & b for a, b in it.combinations(star, 2))
result = {
    "scope": "Literal bounded guard challenges; no full matrix reconstruction or theorem-import verification",
    "marker": {"unrepresented_point_counterexample": True, "full_marker_predicate_comparisons": comparisons,
               "exterior_completion_families": 2, "all_agree": True},
    "stage": {"source_sha256": hashlib.sha256(stage.read_bytes()).hexdigest(),
              "four_to_proper_trace_rejected": absent_four_rejection,
              "proper_trace_restriction_lifts_accepted": 2},
    "low14_matching": {"candidate_graphs": 64, "graphs_satisfying_both_guards": accepted,
                       "every_graph_has_disjoint_pair_and_Q8_leaf_sunflower": True,
                       "triangle_defeats_missing_bipartiteness": True,
                       "star_defeats_missing_maximum_degree_guard": True},
    "result": "PASS"
}
with Path(__file__).with_name("results.json").open("x") as f:
    json.dump(result, f, indent=2)
    f.write("\n")
print(json.dumps(result, indent=2))
