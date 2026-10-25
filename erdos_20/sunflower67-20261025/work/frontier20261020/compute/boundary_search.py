#!/usr/bin/env python3
"""Exact integer encoding diagnostics; solver results require separately checked proof."""
import argparse,itertools,json,time,pathlib,subprocess,hashlib,sys
import numpy as np
P=pathlib.Path(__file__).resolve().parent
TEN=((0,1,2),(0,1,3),(0,2,4),(0,3,5),(0,4,5),(1,2,5),(1,3,4),(1,4,5),(2,3,4),(2,3,5))
mask=lambda x:sum(1<<i for i in x)
C=np.array([mask(t) for t in itertools.combinations(range(16),4)],dtype=np.int64)
T=np.array([mask(t) for t in TEN]+[mask(i+6 for i in t) for t in TEN],dtype=np.int64)
def pairs():
 path=P/'pair_conflicts.npz'
 if path.exists():return np.load(path)['pairs']
 rows=[]
 for i,a in enumerate(C):
  b=C[:i];c=a&b
  conflict=np.zeros(i,dtype=bool)
  for t in T:conflict|=((a&t)==c)&((b&t)==c)
  js=np.nonzero(conflict)[0]
  rows.append(np.column_stack((js,np.full(len(js),i))))
 r=np.concatenate(rows).astype(np.int32);np.savez_compressed(path,pairs=r,candidates=C,high_triples=T);return r
class CNF:
 def __init__(self):self.n=len(C);self.rows=[]
 def add(self,*lits):self.rows.append(tuple(map(int,lits)))
 def new(self):self.n+=1;return self.n
 def totalizer(self,ls,k):
  if len(ls)==1:return ls
  mid=len(ls)//2;a=self.totalizer(ls[:mid],k);b=self.totalizer(ls[mid:],k)
  c=[self.new() for _ in range(min(k,len(a)+len(b)))]
  # Forward sum >= i+j. Indices zero mean the true empty threshold.
  for i in range(len(a)+1):
   for j in range(len(b)+1):
    if 0<i+j<=len(c):self.add(*([-a[i-1]] if i else []),*([-b[j-1]] if j else []),c[i+j-1])
  # Reverse threshold: if A<=i and B<=j, C<=i+j. Treat beyond outputs as false.
  for i in range(len(a)+1):
   for j in range(len(b)+1):
    if i+j<len(c):self.add(*([a[i]] if i<len(a) else []),*([b[j]] if j<len(b) else []),-c[i+j])
  return c
 def eq(self,ls,k):
  out=self.totalizer(ls,k+1)
  if k:self.add(out[k-1])
  if len(out)>k:self.add(-out[k])
 def le(self,ls,k):
  if len(ls)>k:self.add(-self.totalizer(ls,k+1)[k])
 def write(self,path):
  with path.open('w') as f:
   f.write(f'p cnf {self.n} {len(self.rows)}\n')
   for row in self.rows:f.write(' '.join(map(str,row))+' 0\n')
def build_cnf():
 st=time.monotonic();cnf=CNF();idx=np.arange(len(C))+1
 cnf.eq(idx.tolist(),61)
 for v in range(16):cnf.eq(idx[(C&(1<<v))!=0].tolist(),14 if v<12 else 19)
 for size,cap in [(2,6),(3,2)]:
  for q in itertools.combinations(range(16),size):
   m=mask(q);used=sum((int(t)&m)==m for t in T)
   cnf.le(idx[(C&m)==m].tolist(),cap-used)
 for a,b in pairs():cnf.add(-a-1,-b-1)
 path=P/'profile_a_relax.cnf';cnf.write(path)
 info={'variables':cnf.n,'clauses':len(cnf.rows),'candidate_variables':len(C),'pair_conflicts':len(pairs()),'seconds':time.monotonic()-st,'cnf_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'assurance':'encoding diagnostic; no trusted proof checker replay','includes':['exact 61 residual members','exact residual point degrees','pair/triple degree capacities','all one-high two-low sunflower exclusions'],'omits':['all zero-high three-low sunflower exclusions']}
 (P/'encoding.json').write_text(json.dumps(info,indent=2));print(json.dumps(info),flush=True)
def milp(seconds=120):
 from scipy.optimize import milp,Bounds,LinearConstraint
 from scipy.sparse import coo_array
 st=time.monotonic();r=[];c=[];data=[];lb=[];ub=[]
 def add(js,l,h):
  ri=len(lb);r.extend([ri]*len(js));c.extend(js);data.extend([1]*len(js));lb.append(l);ub.append(h)
 add(list(range(len(C))),61,61)
 for v in range(16):add(np.flatnonzero(C&(1<<v)).tolist(),14 if v<12 else 19,14 if v<12 else 19)
 for size,cap in [(2,6),(3,2)]:
  for q in itertools.combinations(range(16),size):
   m=mask(q);used=sum((int(t)&m)==m for t in T)
   add(np.flatnonzero((C&m)==m).tolist(),-np.inf,cap-used)
 for a,b in pairs():add([int(a),int(b)],-np.inf,1)
 A=coo_array((np.array(data,dtype=float),(np.array(r,dtype=np.int32),np.array(c,dtype=np.int32))),shape=(len(lb),len(C))).tocsc()
 print('built',len(lb),'constraints',time.monotonic()-st,flush=True)
 res=milp(np.zeros(len(C)),integrality=np.ones(len(C)),bounds=Bounds(0,1),constraints=LinearConstraint(A,lb,ub),options={'time_limit':seconds,'disp':True})
 out={k:(v.tolist() if isinstance(v,np.ndarray) else v) for k,v in dict(res).items()};out['elapsed_seconds']=time.monotonic()-st;out['assurance']='solver diagnostic only';(P/'milp_result.json').write_text(json.dumps(out,indent=2));print(out,flush=True)
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('mode',choices=['cnf','milp','pairs']);a.add_argument('--seconds',type=int,default=120);ns=a.parse_args()
 if ns.mode=='cnf':build_cnf()
 elif ns.mode=='milp':milp(ns.seconds)
 else:print(pairs().shape)
