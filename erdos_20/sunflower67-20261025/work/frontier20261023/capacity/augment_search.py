from reconstruct import *
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix
from itertools import combinations
import time
P=sorted({erase(f,2) for f in F})
C=[s for s in range(512) if all(s&v!=s for v in P)]
constraints=[]
conf=set()
for i,j in combinations(range(len(C)),2):
 a,b=C[i],C[j]
 if a&b in(a,b) or any(a&b==a&v==b&v for v in P):
  constraints.append(([i,j],1));conf.add((i,j))
for i,j,k in combinations(range(len(C)),3):
 if (i,j) in conf or (i,k) in conf or (j,k) in conf:continue
 a,b,c=C[i],C[j],C[k]
 if a&b==a&c==b&c:constraints.append(([i,j,k],2))
rr=[];cc=[];dd=[]
for row,(cols,_) in enumerate(constraints):
 for col in cols:rr.append(row);cc.append(col);dd.append(1.)
A=coo_matrix((dd,(rr,cc)),shape=(len(constraints),len(C))).tocsc()
con=LinearConstraint(A,-np.inf,np.array([t[1] for t in constraints],float))
results=[]
for idx,(p,q,kind) in enumerate([(0,1,'weighted'),(0,1,'card'),(0,3,'weighted'),(0,4,'weighted'),(0,6,'weighted')]):
 bport=next(t for t in ports(B,19) if t['ports']==[p,q])
 a,b,c,d=bport['matrix'];D=math.sqrt((a-d)**2+4*b*c)
 deriv=[b/D,(1+(d-a)/D)/2,(1+(a-d)/D)/2,c/D]
 weights=np.array([1 if kind=='card' else deriv[((s>>p)&1)*2+((s>>q)&1)] for s in C])
 ans=milp(-weights,integrality=np.ones(len(C)),bounds=Bounds(0,1),constraints=con,options={'time_limit':60,'mip_rel_gap':0})
 selected=[C[i] for i,x in enumerate(ans.x) if x>.5] if ans.x is not None else []
 assert all(sum(C[i] in selected for i in cols)<=rhs for cols,rhs in constraints)
 family=sorted(set(B)|set(selected))
 top=ports(family,19)[0]
 row={'p':p,'q':q,'kind':kind,'status':int(ans.status),'message':ans.message,'selected':selected,'card':len(selected),'top':top}
 results.append(row)
 print(row,flush=True)
 (ROOT/'augment_search.json').write_text(json.dumps(results,indent=2)+'\n')

