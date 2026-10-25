"""Bounded Alpha check, independent literal sunflower test; no producer imports."""
from itertools import combinations
from pathlib import Path
import json

templates = (
    "012 034 134 035 235 145 245", "012 034 234 135 235 145 245",
    "012 134 234 135 235 145 245", "013 024 134 125 235 045 345",
    "023 124 134 125 235 045 345", "014 234 025 125 035 145 345",
    "134 234 125 035 135 045 245", "023 024 034 124 134 015 016",
)
core = [frozenset((h, a, b)) for h in (20, 21)
        for a, b in combinations((22, 23, 24), 2)]
cases = []
total = 0
for index, text in enumerate(templates):
    k = [frozenset(map(int, t)) for t in text.split()]
    support = sorted(set().union(*k))
    safe = [v for v in support if all((a - {v}) & (b - {v})
            for a, b in combinations([a for a in k if v in a], 2))]
    accepted = []
    for size in range(3):
        for shared in combinations(support, size):
            leaves = list(shared) + [30 + j for j in range(2 - size)]
            f = k + core + [frozenset((20, 21, v)) for v in leaves]
            good = not any(a & b == a & c == b & c
                           for a, b, c in combinations(f, 3))
            assert good == set(shared).issubset(safe)
            total += 1
            if good:
                accepted.append(shared)
    cases.append({"template": index, "safe": safe, "accepted": accepted})
result = {"tested": total, "accepted": sum(len(r["accepted"]) for r in cases),
          "criterion_matches_every_test": True, "cases": cases,
          "limitation": "Conditional on the stated I7 catalogue and Q8 core-separation reduction."}
Path(__file__).with_name("independent-gluing.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result))
