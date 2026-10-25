#!/usr/bin/env python3
"""Independent literal template check for the C4 internal-completion lemma.

No producer import, LP, Lean, or claimed new exhaustive I7 classification.
The catalogue's universal completeness and high-link17 split are imports.
"""
import hashlib
import itertools as it
import json
from collections import Counter
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent
CERT = HERE.parents[1] / "frontier20261020/prior-art68/repository/companion/terminal/r16/results/seven_certificate.json"
CERT_SHA = "fe172301b201819c029d9a1b7e8931f516cbd90aa978977118b7853b2ead7164"
I7_TEXT = (
    "012 034 134 035 235 145 245", "012 034 234 135 235 145 245",
    "012 134 234 135 235 145 245", "013 024 134 125 235 045 345",
    "023 124 134 125 235 045 345", "014 234 025 125 035 145 345",
    "134 234 125 035 135 045 245", "023 024 034 124 134 015 016")


def require(value, message):
    if not value:
        raise ValueError(message)


def family(text):
    return frozenset(frozenset(map(int, t)) for t in text.split())


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def validate():
    require(sha(CERT) == CERT_SHA, "Imported I7 literal certificate changed")
    rows = json.loads(CERT.read_text())["rows"]
    require([r["id"] for r in rows] == list(range(8)), "Wrong I7 domain")
    models = []
    for i, text in enumerate(I7_TEXT):
        L = family(text)
        require(L == frozenset(map(frozenset, rows[i]["blocks"])), "I7 literal mismatch")
        models.append((f"H{i}", L))
    p10 = family("012 015 023 034 045 124 134 135 235 245")
    models.append(("P10", p10))
    for j, removed in enumerate(it.combinations(sorted(p10, key=lambda t:tuple(sorted(t))), 1)):
        models.append((f"P9-{j:02d}", p10 - frozenset(removed)))
    for j, removed in enumerate(it.combinations(sorted(p10, key=lambda t:tuple(sorted(t))), 2)):
        models.append((f"P8-{j:02d}", p10 - frozenset(removed)))
    models.append(("Q8", family("023 024 034 123 124 134 015 016")))
    records, points_checked = [], 0
    for name, L in models:
        require(all(A & B for A, B in it.combinations(L, 2)), "Nonintersecting template")
        require(all(not (A & B == A & C == B & C) for A, B, C in it.combinations(L, 3)),
                "Template has a sunflower")
        for x in sorted(set().union(*L)):
            points_checked += 1
            E = [T - {x} for T in L if x in T]
            degree = Counter(v for edge in E for v in edge)
            if name.startswith(("P9-", "P8-")) and len(E) == 4:
                require(sorted(degree.values()) == [1,1,2,2,2],
                        "Degree4 P9/P8 point-link is not the required P5")
            if len(E) != 4 or sorted(degree.values()) != [2,2,2,2]:
                continue
            W = frozenset(degree)
            # A simple four-edge graph with these degrees is exactly C4.
            completions = sorted((sorted(T) for T in L if T <= W))
            require(bool(completions), "A C4 point lacks an internal completion")
            records.append(dict(template=name, point=x, neighbours=sorted(W),
                                edges=sorted(map(sorted, E)), completions=completions))
    require({(r["template"], r["point"]) for r in records}
            == {("H1",5), ("H2",3), ("H2",4), ("H2",5), ("H7",4),
                ("Q8",2), ("Q8",3), ("Q8",4)}, "Unexpected complete C4 point domain")
    return dict(result="PASS_LITERAL_C4_TEMPLATE_COMPLETIONS", models=len(models),
                points_checked=points_checked, C4_points=records,
                imported_I7_certificate=dict(path=str(CERT), sha256=CERT_SHA),
                premises=["Universal I7 and I8 classification on arbitrary support is imported.",
                          "Complete degree17 SF3 link has separated P10+I7 or P9+I8 form.",
                          "The pair-link is complete C4, not merely an embedded C4."],
                assurance="Exact literal template validation only; no new classification, solver, Lean, or complete branch proof.")


def main():
    started = time.monotonic()
    output = HERE / "D17-C4-completion-literal.json"
    require(not output.exists(), "Refusing to overwrite receipt")
    result = validate()
    result.update(source_sha256=sha(__file__),
                  ordinary_bridge_sha256=sha(HERE / "D17-C4-internal-completion.md"),
                  seconds=time.monotonic()-started)
    with output.open("x") as f:
        json.dump(result, f, indent=2)
        f.write("\n")
    print(json.dumps(dict(result=result["result"], models=result["models"],
                         C4_points=len(result["C4_points"]), seconds=result["seconds"],
                         output=str(output), source_sha256=result["source_sha256"])))


if __name__ == "__main__":
    main()
