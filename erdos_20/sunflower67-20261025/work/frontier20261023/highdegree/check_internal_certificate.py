#!/usr/bin/env python3
"""Independent exact checker of the compressed I00 coefficient cover.

No solver, numpy, source model, table import, or floating arithmetic. This checks
the finite cover, not the prior universal geometry used by its mathematical rows.
"""
from itertools import combinations, product
from pathlib import Path
from collections import Counter
import hashlib,json,time

HERE=Path(__file__).resolve().parent
start=time.monotonic()
Y=frozenset(range(6));Z=frozenset(range(6,12));M=frozenset((0,1,2,3))
D=tuple(frozenset(map(int,s)) for s in '012 015 023 034 045 124 134 135 235 245'.split())
DZ=tuple(frozenset(v+6 for v in t) for t in D)
LINK=D+DZ

def exact(S,A,T):return int(S&A==T)
def coefficient(S):
    q=5*int({0,2}<=S)
    q+=5*sum(T<=S for T in DZ)
    q+=2*exact(S,frozenset((0,1,2)),frozenset((1,)))
    for anchor,trace,w in [((0,1,5),(0,5),3),((0,3,4),(0,4),3),
                            ((0,4,5),(0,4),2),((0,4,5),(0,5),2),
                            ((1,2,4),(2,4),3),((2,4,5),(2,4),2),
                            ((2,4,5),(2,5),2)]:
        q+=w*exact(S,frozenset(anchor),frozenset(trace))
    q+=2*exact(S,M,frozenset((3,)))
    q+=sum(v in S and not(len(S)==4 and S<=Y) for v in (1,3))
    # The one nontrivial local inequality, written on anchor {x,1,3,5}.
    T=frozenset((1,3,5))
    for trace,w in [((1,3),3),((1,5),2),((3,5),2),((1,3,5),3),((1,),2),((3,),2)]:
        q+=w*exact(S,T,frozenset(trace))
    q+=3*exact(S,frozenset((2,3,5)),frozenset((2,5)))
    return int(q)

admissible=[];excluded=[];hist=Counter()
for k in range(5):
    for tup in combinations(range(12),k):
        S=frozenset(tup)
        witnesses=[i for i,T in enumerate(LINK) if S&T==S&M==T&M]
        if witnesses:
            excluded.append({'trace':list(tup),'blocking_cone_index':witnesses[0]})
        else:
            q=coefficient(S)
            assert q>=5,(tup,q)
            admissible.append({'trace':list(tup),'weight':q});hist[q]+=1
assert coefficient(M)==8
assert len(admissible)+len(excluded)==sum(1 for k in range(5) for _ in combinations(range(12),k))==794
rhs=5*4+10*5+2*10+(3+3+2+2+3+2+2)*3+2*10+2*10+51+3*3
assert rhs==241
# Weak elementary interface sufficient for the local51 inequality. This is
# reconstructed independently of the imported signature table.
local_count=0;best=0;maximizers=[]
for a,b,c,e,s,t in product(range(4),range(4),range(4),range(2),range(11),range(11)):
    d1=5+a+b+e+s;d2=5+a+c+e+t
    if d1>20 or d2>20:continue
    if s<=7 and d1>17:continue
    if t<=7 and d2>17:continue
    if s>=8 and (a>2 or b>2):continue
    if t>=8 and (a>2 or c>2):continue
    if s>=8 and t>=8 and (e!=0 or a>1):continue
    if (d1==20 or d2==20) and (a!=2 or e!=1):continue
    score=3*a+2*b+2*c+3*e+2*s+2*t
    assert score<=51,(a,b,c,e,s,t,score)
    local_count+=1
    if score>best:best=score;maximizers=[]
    if score==best:maximizers.append([a,b,c,e,s,t])
out={'assurance':'exact finite coefficient-cover certificate; universal geometry bridge stated separately',
     'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'trace_domain':794,'admissible_count':len(admissible),'excluded_count':len(excluded),
     'coefficient_histogram':dict(sorted(hist.items())),'marker_coefficient':8,
     'weighted_rhs':241,'residual_inequality':'5*r+3 <=241; hence r<=47 for integral r',
     'family_inequality':'20+r<=67, conditional on universal row premises',
     'local_weak_domain':local_count,'local_max':best,'local_maximizers':maximizers,
     'admissible':admissible,'excluded':excluded,'seconds':time.monotonic()-start}
(HERE/'internal_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ('admissible','excluded','local_maximizers')},indent=2))
