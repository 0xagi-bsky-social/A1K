"""Self-contained exact checks via seed conditions and a proved union lemma.
Does not import any other project checker or execute upstream code.
"""
from pathlib import Path
from itertools import combinations, permutations, product
from fractions import Fraction
from hashlib import sha256
import json,time
P=Path(__file__).resolve().parent
E=list(combinations(range(5),2)); ALL=(1<<10)-1
def em(edges):return sum(1<<E.index(tuple(sorted(e))) for e in set(tuple(sorted(e)) for e in edges))
F=set()
for v in range(5):F.add(em((v,w) for w in range(5) if w!=v))
for part in combinations(range(5),2):F.add(em((v,w) for v in part for w in range(5) if w not in part))
for v,w,t in permutations(range(5),3):
 leaves=[z for z in range(5) if z not in(v,w,t)]
 F.add(ALL^em([(v,w),(w,t)]+[(v,z) for z in leaves]))
H={sum(1<<((a*x+b)%11) for x in S) for S in [(0,1,2,3,4,5,6),(0,1,2,3,4,6,7),(0,1,2,6,9)] for a in [1,3,4,5,9] for b in range(11)}
A={118,223,251,253,319,333,379,403,445,446,478,487,491,494,501}
def erase(s,p):return(s&((1<<p)-1))|((s>>(p+1))<<p)
def insert_zero(s,p):return(s&((1<<p)-1))|((s>>p)<<(p+1))
def status(S,n):
 S=set(S);comp=0;sf=0
 for a,b in combinations(S,2):
  if a&b in(a,b):comp+=1
  core=a&b;free=((1<<n)-1)^(a|b);z=free
  while True:
   c=core|z
   if c not in(a,b) and c in S:sf+=1
   if not z:break
   z=(z-1)&free
 return {'containments':comp,'sunflower_triples':sf//3}
checks={}
checks['F']=status(F,10);checks['H']=status(H,11)
assert len(F)==75 and len(H)==121
assert checks['F']==checks['H']=={'containments':0,'sunflower_triples':0}
checks['control_sunflower']=status({1,2,4},3)
checks['control_containment']=status({1,3},2)
assert checks['control_sunflower']['sunflower_triples']==1
assert checks['control_containment']['containments']==1
HP={erase(h,0) for h in H}
assert len(HP)==121 and min(x.bit_count() for x in HP)>0
checks['punctured_H_min_pair_intersection']=min((a&b).bit_count() for a,b in combinations(HP,2))
assert checks['punctured_H_min_pair_intersection']>=1
FP={erase(f,2) for f in F}
checks['A']=status(A,9)
assert len(A)==15 and checks['A']=={'containments':0,'sunflower_triples':0}
checks['A_not_contained_in_F_projection']=all(a&f!=a for a,f in product(A,FP))
checks['two_A_one_F_projection_no_sunflower']=all(a&b!=a&f or a&b!=b&f for a,b in combinations(A,2) for f in FP)
assert checks['A_not_contained_in_F_projection'] and checks['two_A_one_F_projection_no_sunflower']
# Explicit independent assembly of Q2 and Q3 from 75+15 local rectangles.
def project_core(s):return sum(1<<j for j,i in enumerate([0,1,4,5,6,7,8,9]) if s>>i&1)
Ht={v:[erase(h,0) for h in H if h&1==v] for v in [0,1]}
base={project_core(f)|(h2<<8)|(h3<<18) for f in F for h2 in Ht[1-((f>>2)&1)] for h3 in Ht[1-((f>>3)&1)]}
E2={project_core(insert_zero(a,2))|(h3<<18) for a in A for h3 in Ht[1-((insert_zero(a,2)>>3)&1)]}
swap=[0,1,2,4,3]
A3=set()
for a in A:
 s=insert_zero(a,2)
 t=em((swap[u],swap[v]) for i,(u,v) in enumerate(E) if s>>i&1)
 A3.add(erase(t,3))
E3={project_core(insert_zero(a,3))|(h2<<8) for a in A3 for h2 in Ht[1-((insert_zero(a,3)>>2)&1)]}
assert base.isdisjoint(E2) and base.isdisjoint(E3) and E2.isdisjoint(E3)
C=base|E2|E3
assert [len(base),len(E2),len(E3),len(C)]==[250659,806,806,252271]
readC=[int(s) for s in (P/'candidate28.masks').read_text().splitlines()]
assert len(readC)==len(set(readC)) and set(readC)==C
# Omission control against recomputed literal construction.
assert set(readC[:-1])!=C
N=[sum(2*(s&1)+((s>>1)&1)==v for s in C) for v in range(4)]
assert N==[33948,64728,64728,88867]
assert [N[2],N[3],N[0],N[1]]==[64728,88867,33948,64728]
badN=N.copy();badN[0]+=1
assert badN!=[33948,64728,64728,88867]
# Integer-only rate comparison across different root exponents.
p,q=156785,100000
new_delta=p**26-64728*q**26
old_delta=p**17-1127*q**17
new_margin=3016856916*q**52-new_delta**2
old_margin=old_delta**2-925536*q**34
assert new_delta>0 and old_delta>0 and new_margin>0 and old_margin>0
# Tight rational interval, still exact integer arithmetic.
def new_rate_gt(p,q):
 d=p**26-64728*q**26
 return d<0 or d*d<3016856916*q**52
def new_rate_lt(p,q):
 d=p**26-64728*q**26
 return d>0 and d*d>3016856916*q**52
assert new_rate_gt(156785134269,10**11)
assert new_rate_lt(156785134270,10**11)
record={'result':'PASS','method':'seed checks plus gluing and simultaneous-augmentation union lemma; no project imports','checks':checks,'cardinalities':{'base':len(base),'E2':len(E2),'E3':len(E3),'candidate':len(C)},'port_counts_N00_N01_N10_N11':N,'transfer_matrix':[[64728,88867],[33948,64728]],'root_exponent':26,'radicand':3016856916,'comparison_rational':[p,q],'positive_integer_margins':{'new':str(new_margin),'old':str(old_margin)},'witness_sha256':sha256((P/'candidate28.masks').read_bytes()).hexdigest(),'assurance':'certificate-diagnostic; written general proof accompanies this check; not Lean kernel verification or independent reproduction'}
(P/'verify_structural28.result.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='positive_integer_margins'},indent=2))

