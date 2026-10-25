"""Fresh final Chief controls; standard library, no proof-producer imports."""
from itertools import combinations, permutations, product
from collections import Counter
from pathlib import Path
import json

P = {frozenset(map(int, s)) for s in
     '012 015 023 034 045 124 134 135 235 245'.split()}
internal = [frozenset(s) for s in combinations(range(6), 4)]
cones = [t | {6} for t in sorted(P, key=lambda t: tuple(sorted(t)))]
all_sets = cones + internal
bad = set()
for inds in combinations(range(25), 3):
    a, b, c = [all_sets[i] for i in inds]
    if a & b == a & c == b & c:
        bits = sum(1 << (i - 10) for i in inds if i >= 10)
        assert bits
        bad.add(bits)
admissible = {m for m in range(1 << 15)
              if not any(m & b == b for b in bad)}
autos = [p for p in permutations(range(6))
         if {frozenset(p[v] for v in t) for t in P} == P]
index = {t: i for i, t in enumerate(internal)}
maps = [[index[frozenset(p[v] for v in t)] for t in internal] for p in autos]
unseen = set(admissible)
orbits = []
while unseen:
    m = min(unseen)
    orbit = {sum(1 << mp[i] for i in range(15) if m & (1 << i)) for mp in maps}
    assert orbit <= admissible
    unseen -= orbit
    orbits.append(len(orbit))
incidence = {str(k): dict(Counter(sum(bool(t & s) for t in P)
             for s in map(frozenset, combinations(range(6), k)))) for k in (1, 2, 3)}
assert all(any(not (t & set(pair)) for t in P) for pair in combinations(range(6), 2))
feasible = [(5*h+8*p+10*e, h, p, e) for h in range(52)
            for p in range(19) for e in range(52-h-p)
            if h+2*p+3*e <= 60 and p+e >= 24]
best = max(feasible)
assert len(admissible) == 292 and len(autos) == 60 and len(orbits) == 13
assert best[0] == 234 < 10*(41-17)

adj = [[j for j in range(8) if (j-i) % 8 in (3,4,5)] for i in range(8)]
for v in range(8):
    counts = [sum(j in adj[i] for i in (v,(v+3)%8,(v+5)%8)) for j in range(8)]
    assert counts == [1+(j==v) for j in range(8)]
profiles = [r for r in product(range(3), repeat=8) if sum(r) == 4]
for r in profiles:
    a = [7+r[i]+r[(i+3)%8]+r[(i+5)%8] for i in range(8)]
    b = [sum(a[j] for j in adj[i]) for i in range(8)]
    assert sum(a) == 68 and b == [25+x for x in r]
    assert min(a) >= 1
control_a = [0,15,13,0,12,0,15,13]
control_b = [sum(control_a[j] for j in adj[i]) for i in range(8)]
ind = [s for m in range(256) if (s := [i for i in range(8) if m >> i & 1])
       and all(j not in adj[i] for i,j in combinations(s,2))]
control_alpha = max(sum(control_a[i] for i in s) for s in ind)
assert sum(control_a) == 68 and control_alpha == 28
assert min(control_b[i] for i in range(8) if control_a[i]) == 25
assert min(control_a) == 0

outer_relaxed = [(s,p,t,q) for s in range(33) for p in range(19)
                 for t in range(13) for q in range(2)
                 if s+2*p+3*t+4*q<=37 and 3*s+4*p+4*t+4*q>=104]
outer_guarded = [x for x in outer_relaxed if x[1] == 0 or x[0] <= 30]
hub_relaxed = [(a,b,c,y,t) for a in range(9) for b in range(a,9)
               for c in range(b,9) for y in range(9) for t in range(3)
               if y+3*t<=8 and y+t>=1+b+c and y<=2*a+b]
hub_guarded = [x for x in hub_relaxed if x[3]+3<=2*x[0]+x[1]]
edges = [frozenset(x) for x in [(4,5),(4,6),(5,6),(0,2),(0,3)]]
covers = [s for s in combinations([0,2,3,4,5,6,99],3)
          if all(set(s)&e for e in edges)]
assert covers == [(0,4,5),(0,4,6),(0,5,6)]
assert not outer_guarded and outer_relaxed
assert not hub_guarded and hub_relaxed

result = {
    'd17_internal': {'admissible_assignments':len(admissible),
                    'automorphisms':len(autos),'orbit_sizes':sorted(orbits),
                    'trace_meeting_counts':incidence,
                    'maximum_relaxed_W':best[0],
                    'maximizing_H_P_E':best[1:], 'required_W':240},
    'a3': {'profiles':len(profiles), 'coefficient_identity_verified':True,
           'h28_counterexample_fibres':control_a,'adjacent_masses':control_b,
           'independence_number':control_alpha,
           'minimum_occupied_adjacent_mass':25,
           'jin_strict_margin':25*11-4*68},
    'deletions': {'outer_guarded_solutions':len(outer_guarded),
                  'outer_without_positive_pair_guard_example':outer_relaxed[0],
                  'hub_guarded_solutions':len(hub_guarded),
                  'hub_without_strict_pair_guard_example':hub_relaxed[0],
                  'B4_triangle_path_three_covers':covers},
    'limits': 'Bounded independent controls, not full coefficient, tree or historical H27 replay.'
}
Path(__file__).with_name('results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
