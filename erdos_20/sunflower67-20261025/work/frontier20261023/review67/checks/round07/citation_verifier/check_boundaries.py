"""Small independent reconstructions of committed Alpha boundary examples."""
import itertools
import json

masses = (0, 15, 13, 0, 12, 0, 15, 13)
edges = {frozenset((i, j)) for i in range(8) for j in range(i + 1, 8)
         if (j-i) % 8 in {3, 4, 5}}
adjacent = [sum(masses[j] for j in range(8) if frozenset((i,j)) in edges)
            for i in range(8)]
independent = []
for mask in range(256):
    support = [i for i in range(8) if mask & (1 << i)]
    if not any(frozenset(pair) in edges for pair in itertools.combinations(support, 2)):
        independent.append(sum(masses[i] for i in support))
graph = {
    "masses": masses, "order": sum(masses), "adjacent_masses": adjacent,
    "minimum_actual_degree": min(adjacent[i] for i in range(8) if masses[i]),
    "independence_number": max(independent),
    "triangle_count_in_image": sum(all(frozenset(p) in edges for p in itertools.combinations(t,2))
                                    for t in itertools.combinations(range(8),3)),
    "empty_fibres": [i for i in range(8) if not masses[i]],
}
p8 = [frozenset(map(int, s)) for s in "023 034 045 124 134 135 235 245".split()]
h7 = [frozenset(int(c)+6 for c in s) for s in "023 024 034 124 134 015 016".split()]
family = p8+h7
sunflowers = [(sorted(a), sorted(b), sorted(c)) for a,b,c in itertools.combinations(family,3)
              if a & b == a & c == b & c]
rho = max(sum(not (a & b) for b in family) for a in family)
triple_example = {
    "family": [sorted(t) for t in family], "members": len(set(family)),
    "support": len(set().union(*family)), "rho": rho,
    "sunflower_count": len(sunflowers),
}
assert graph["order"] == 68 and graph["minimum_actual_degree"] == 25
assert graph["independence_number"] == 28 and graph["triangle_count_in_image"] == 0
assert triple_example["members"] == 15 and triple_example["support"] == 13
assert rho == 8 and not sunflowers
print(json.dumps({"graph_boundary": graph, "triple_boundary": triple_example}, indent=2))
