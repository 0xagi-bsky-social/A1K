import itertools,json
from pathlib import Path
D=[frozenset(t) for t in [(0,1,2),(1,2,3),(0,2,4),(0,1,5),(0,3,4),(0,3,5),(1,4,3),(1,4,5),(2,5,3),(2,5,4)]]
E=[t-{0} for t in D if 0 in t]
Db=[frozenset(v+6 for v in t) for t in D]
Eb=[t-{6} for t in Db if 6 in t]
x=12; R=frozenset([0,6,13,14]);stars=[t|{x} for t in D+Db];coords=list(itertools.product(E,Eb));C=[a|b for a,b in coords]
def sun(a,b,c):return a&b==a&c==b&c
assert len(E)==len(Eb)==5
assert all(not sun(*t) for t in itertools.combinations(stars+[R],3))
pair_mismatch=[]; adj=[set() for _ in C]
for i,j in itertools.combinations(range(25),2):
 bad=any(sun(C[i],C[j],t) for t in stars+[R]);pred=bool(coords[i][0]&coords[j][0]) and bool(coords[i][1]&coords[j][1])
 if (not bad)!=pred:pair_mismatch.append([i,j])
 if not bad:adj[i].add(j);adj[j].add(i)
best=[]
def clique(chosen,cand):
 global best
 if len(chosen)+len(cand)<=len(best):return
 if not cand:
  if len(chosen)>len(best):best=chosen
  return
 while cand:
  v=cand.pop();clique(chosen+[v],cand&adj[v])
clique([],set(range(25)))
naive=[a|b for a,b in coords if a==E[0]]
assert len(naive)==5 and all(a&b for a,b in itertools.combinations(naive,2))
assert not pair_mismatch and len(best)==4
out={'candidate_completions':len(C),'pair_checks':300,'coordinate_compatibility_mismatches':pair_mismatch,'maximum_compatible_clique':len(best),'naive_intersecting_only_counterexample_size':len(naive),'scope':'Canonical local diagnostic only; no universal proof or normalization claim'}
print(json.dumps(out,indent=2));Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
