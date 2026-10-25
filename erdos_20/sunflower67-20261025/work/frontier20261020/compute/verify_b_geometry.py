#!/usr/bin/env python3
"""Independent exact-integer check of B candidate filter; not Lean proof."""
import itertools as I,json,pathlib,time,hashlib
import numpy as np
P=pathlib.Path(__file__).resolve().parent
start=time.monotonic()
def mask(S):return sum(1<<i for i in S)
def lift(T,S):return mask(S[i] for i in range(6) if T>>i&1)
def sf(a,b,c):return a&b==a&c==b&c
TEN=[mask(x) for x in [(0,1,2),(0,1,3),(0,2,4),(0,3,5),(0,4,5),(1,2,5),(1,3,4),(1,4,5),(2,3,4),(2,3,5)]]
T=TEN+[t<<6 for t in TEN]
# Re-enumerate designs via all one-from-complementary-pair choices, independent of permutation orbit.
trip6=[mask(x) for x in I.combinations(range(6),3)];comp=[(t,63^t) for t in trip6 if t<(63^t)]
designs=[]
for bits in range(1024):
 D=[p[(bits>>j)&1] for j,p in enumerate(comp)]
 if all(sum((t&p)==p for t in D)==2 for p in map(mask,I.combinations(range(6),2))):designs.append(D)
assert len(designs)==12
# All residual candidates encoded as a Python big-integer set; each S triple gets its compatibility set.
R=np.array([mask(x) for x in I.combinations(range(15),4)],dtype=np.int64); full=(1<<len(R))-1
allowed={}
for S in map(mask,I.combinations(range(15),3)):
 good=np.ones(len(R),dtype=bool)
 for t in T:good&=~(((t&S)==(t&R))&((t&S)==(S&R)))
 allowed[S]=sum(1<<int(i) for i in np.flatnonzero(good))
# Verify all quotient cases with different representation and different design construction.
parent=json.loads((P.parent/'b_geometry_data.json').read_text());hist={};maxcase=None;nonempty=[]
for A,B in parent['support_partition_representatives']:
 ptsA=[i for i in range(15) if A>>i&1];ptsB=[i for i in range(15) if B>>i&1]
 for da,db in I.product(designs,repeat=2):
  can=full
  for d,S in [(da,ptsA),(db,ptsB)]:
   for t in d:can &= allowed[lift(t,S)]
  n=can.bit_count();hist[n]=hist.get(n,0)+1
  if n:nonempty.append({'A':A,'B':B,'designA':da,'designB':db,'count':n,'candidates':[int(R[i]) for i in range(len(R)) if can>>i&1]})
  if maxcase is None or n>maxcase['count']:maxcase={'A':A,'B':B,'designA':da,'designB':db,'count':n,'candidates':[int(R[i]) for i in range(len(R)) if can>>i&1]}
# Independently verify every unquotiented unordered support partition reduces into representative list.
autos=[p for p in I.permutations(range(6)) if sorted(lift(t,p) for t in TEN)==sorted(TEN)]
colorcanon={c:min(tuple(c[p[i]] for i in range(6)) for p in autos) for c in I.product(range(3),repeat=6)}
reps=set(map(tuple,parent['support_partition_representatives']));coverage=0
for aa in I.combinations(range(15),6):
 A=mask(aa);outside=[i for i in range(15) if not A>>i&1]
 for bb in I.combinations(outside,6):
  B=mask(bb)
  if A>B:continue
  color=tuple(1 if A>>i&1 else 2 if B>>i&1 else 0 for i in range(15))
  can=colorcanon[color[:6]]+colorcanon[color[6:12]]+tuple(sorted(color[12:]))
  key=tuple(sorted((mask(i for i,c in enumerate(can) if c==1),mask(i for i,c in enumerate(can) if c==2))))
  assert key in reps,(A,B,key)
  coverage+=1
assert coverage==210210
# Direct full-set verification of all admitted four-sets in the maximum case.
A=[i for i in range(15) if maxcase['A']>>i&1];B=[i for i in range(15) if maxcase['B']>>i&1]
Hs=[t|(1<<15) for t in T]
Ks=[lift(t,A)|(1<<16) for t in maxcase['designA']]+[lift(t,B)|(1<<16) for t in maxcase['designB']]
for r in R:
 good=not any(sf(h,k,int(r)) for h in Hs for k in Ks)
 assert good==(int(r) in maxcase['candidates'])
output={'assurance':'certificate-diagnostic; independent implementation in same agent/provider, not Lean','histogram':hist,'max_case':maxcase,'nonempty_cases':nonempty,'labelled_support_partitions_covered':coverage,'orbit_representatives':len(reps),'designs_by_complement_choice':len(designs),'cases_checked':sum(hist.values()),'seconds':time.monotonic()-start,'source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
(P/'verify_b_geometry.json').write_text(json.dumps(output,indent=2));print(json.dumps(output),flush=True)
