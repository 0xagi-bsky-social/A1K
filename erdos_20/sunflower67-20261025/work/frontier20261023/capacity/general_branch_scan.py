"""General simultaneous branch augmentation; exact integer weighted counts.
The square-root rates here are ranking diagnostics only.
"""
from reconstruct import *
from itertools import permutations,combinations,product
import json,math
A=sorted(set(Bp)-set(B))
T={i:set() for i in range(10)}
for perm in permutations(range(5)):
 edge=EDGES.index(tuple(sorted((perm[0],perm[3]))))
 t=[]
 for a in A:
  lift=(a&3)|((a>>2)<<3)
  t.append(mask(EDGES.index(tuple(sorted((perm[u],perm[v])))) for j,(u,v) in enumerate(EDGES) if lift>>j&1))
 T[edge].add(tuple(sorted(t)))
T={k:sorted(v) for k,v in T.items()}
def weighted(fam,branches,ports):
 N=[0]*4
 for f in fam:
  w=1
  for j in branches:w*=46 if f>>j&1 else 75
  N[2*((f>>ports[0])&1)+((f>>ports[1])&1)]+=w
 return N
def rate(N,cost):
 a,b,c,d=N[2],N[3],N[0],N[1]
 return ((a+d+math.sqrt((a-d)**2+4*b*c))/2)**(1/cost)
best=0;records=[];by_m={}
for pp in [(0,1),(0,7)]:
 free=[i for i in range(10) if i not in pp]
 for m in range(9):
  for S in combinations(free,m):
   base=weighted(F,S,pp)
   extra=[[weighted(t,[j for j in S if j!=i],pp) for t in T[i]] for i in S]
   for choices in product(range(2),repeat=m):
    N=[base[k]+sum(opts[c][k] for opts,c in zip(extra,choices)) for k in range(4)]
    r=rate(N,8+9*m)
    row={'ports':pp,'branches':S,'templates':choices,'N':N,'exponent':8+9*m,'size':sum(N),'rate_diagnostic':r}
    if m not in by_m or r>by_m[m]['rate_diagnostic']:by_m[m]=row
    if r>best+1e-14:best=r;records.append(row);print(row,flush=True)
out={'template_lifted_masks':T,'records':records,'best_by_m':by_m,'status':'exploratory ranking; exact counts; all candidates satisfy the general union theorem'}
(ROOT/'general_branch_scan.json').write_text(json.dumps(out,indent=2)+'\n')
print('best_by_m',json.dumps(by_m,indent=2),flush=True)

