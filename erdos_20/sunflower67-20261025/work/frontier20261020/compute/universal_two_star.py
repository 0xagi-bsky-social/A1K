#!/usr/bin/env python3
"""All relative canonical20-star geometries + four fresh residual points.
Exact bitset diagnostic, not a Lean certificate.
"""
import itertools as it,json,pathlib,time,hashlib
import numpy as np
P=pathlib.Path(__file__).resolve().parent
st=time.monotonic()
m=lambda xs:sum(1<<i for i in xs)
TEN=[m(x) for x in [(0,1,2),(0,1,3),(0,2,4),(0,3,5),(0,4,5),(1,2,5),(1,3,4),(1,4,5),(2,3,4),(2,3,5)]]
T=TEN+[t<<6 for t in TEN]
def lift(t,pts):return m(pts[i] for i in range(6) if t>>i&1)
autos=[p for p in it.permutations(range(6)) if sorted(lift(t,p) for t in TEN)==sorted(TEN)]
reps=sorted({min(tuple(c[p[i]] for i in range(6)) for p in autos) for c in it.product(range(3),repeat=6)})
trip=[m(x) for x in it.combinations(range(6),3)];cp=[(t,63^t) for t in trip if t<(63^t)]
designs=[]
for bits in range(1024):
 D=[p[(bits>>j)&1] for j,p in enumerate(cp)]
 if all(sum((t&p)==p for t in D)==2 for p in map(m,it.combinations(range(6),2))):designs.append(D)
assert len(designs)==12
parts=set()
for a,b in it.product(reps,repeat=2):
 c=a+b; n1=6-c.count(1);n2=6-c.count(2)
 if min(n1,n2)<0 or n1+n2>12:continue
 c=c+(1,)*n1+(2,)*n2+(0,)*(12-n1-n2)
 A=m(i for i,v in enumerate(c) if v==1);B=m(i for i,v in enumerate(c) if v==2)
 parts.add(tuple(sorted((A,B))))
parts=sorted(parts)
print(json.dumps({'phase':'geometry','partitions':len(parts),'cases':144*len(parts),'seconds':time.monotonic()-st}),flush=True)
R=np.array([m(x) for x in it.combinations(range(28),4)],dtype=np.int64);full=(1<<len(R))-1
allowed={}
for j,S in enumerate(map(m,it.combinations(range(24),3))):
 good=np.ones(len(R),dtype=bool)
 for t in T:good&=~(((t&S)==(t&R))&((t&S)==(S&R)))
 allowed[S]=int.from_bytes(np.packbits(good,bitorder='little').tobytes(),'little')
print(json.dumps({'phase':'compatibility','R':len(R),'triples':len(allowed),'seconds':time.monotonic()-st}),flush=True)
hist={};nonempty=[];byintersection={}
for A,B in parts:
 pa=[i for i in range(24) if A>>i&1];pb=[i for i in range(24) if B>>i&1]
 for da,db in it.product(designs,repeat=2):
  can=full
  for d,ps in [(da,pa),(db,pb)]:
   for t in d:can&=allowed[lift(t,ps)]
  n=can.bit_count();hist[n]=hist.get(n,0)+1
  k=((A|B)&4095).bit_count();tab=byintersection.setdefault(k,{});tab[n]=tab.get(n,0)+1
  if n:nonempty.append({'A':A,'B':B,'designA':da,'designB':db,'intersection':k,'count':n,'candidates':[int(R[i]) for i in range(len(R)) if can>>i&1]})
out={'assurance':'certificate-diagnostic; not Lean checked','universe_lemma_required':'Normalize first20link to12points, second20link adds≤12points, a tested residual4set adds≤4points; permutations fix firstlink and relabel otherpoints. Colororbits under A5×A5 and outsidepermutations cover all relative componentpartitions.','source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'partitions':len(parts),'cases':len(parts)*144,'candidate_R':len(R),'histogram':hist,'by_support_intersection':byintersection,'nonempty':nonempty,'seconds':time.monotonic()-st}
(P/'universal_two_star.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k!='nonempty'}),flush=True)
