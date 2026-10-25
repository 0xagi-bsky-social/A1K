from reconstruct import *
from itertools import product
import json, math
# Each optional pendant is a proven rooted family; weight at occupied core point
# = pendant avoid-count; at unoccupied core point = pendant contain-count.
leaves=[('none',1,1,0),('F',31,44,8),('H',46,75,9)]
# F has transitive adjacent-pair and disjoint-pair port types.
best=(0,None);records=[]
for core,n,portpairs in [('F',10,[(0,1),(0,7)]),('H',11,[(0,1)])]:
 fam=F if core=='F' else H
 for p,q in portpairs:
  free=[j for j in range(n) if j not in (p,q)]
  for choice in product(range(3),repeat=len(free)):
   costs=sum(leaves[t][3] for t in choice);N=[0]*4
   for s in fam:
    w=1
    for j,t in zip(free,choice): w*=leaves[t][1 if s>>j&1 else 2]
    N[((s>>p)&1)*2+((s>>q)&1)]+=w
   a,b,c,d=N[2],N[3],N[0],N[1];exp=n-2+costs
   lograte=math.log((a+d+math.sqrt((a-d)**2+4*b*c))/2)/exp
   if lograte>best[0]+1e-14:
    row={'core':core,'ports':[p,q],'attachments':[(j,leaves[t][0]) for j,t in zip(free,choice) if t],'matrix':[a,b,c,d],'exponent':exp,'exploratory_rate':math.exp(lograte)}
    records.append(row);best=(lograte,row);print(row,flush=True)
(ROOT/'pendant_scan.json').write_text(json.dumps({'leaves':leaves,'records':records},indent=2)+'\n')

