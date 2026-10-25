#!/usr/bin/env python3
"""Independent integer trace cover for the degree19 singleton-Y equality leaf.

No solver, model import, or signature catalogue. Source receipt weights are
decoded against independently enumerated basic row labels and central features.
All local rows here are ordinary exact-pair/triple capacities.
"""
from pathlib import Path
from itertools import combinations,permutations
import json,hashlib
P=Path(__file__).resolve().parent
mask=lambda vs:sum(1<<v for v in vs)
D=tuple(mask(map(int,t)) for t in '012 015 023 034 045 124 134 135 235 245'.split())
LINK=D+tuple(t<<6 for t in D[1:]);X=1<<13;STAR=tuple(X|t for t in LINK)
M=15;Y=63;Z=63<<6
src=P/'degree19/Ypattern01-Z.json';d=json.loads(src.read_text())['dual'];scale=d['scale']
rows=[]
for _,w,label in d['ineq']:
    assert w%scale==0;w//=scale
    kind=label[0]
    if kind=='incidence':
        u=label[1];cap={1:19,2:6,3:2}[u.bit_count()]
        rhs=cap-sum(T&u==u for T in LINK)
        rows.append((w,rhs,kind,u,0))
    elif kind=='exact':
        A,u=label[1:];assert A in STAR+(M,) and u&A==u
        rhs={1:10,2:3,3:1}[u.bit_count()]-sum(B&A==u for B in STAR)
        rows.append((w,rhs,kind,A,u))
    else:
        assert kind=='C5' and label[1]==3 and w==1
        rows.append((1,10,kind,3,0))
local=[]
for k,T in enumerate(LINK):
    es={i-8*k:w//scale for i,w in d['eq'] if 8*k<=i<8*k+8}
    assert all(w%scale==0 for i,w in d['eq'])
    if not es:continue
    pts=[v for v in range(12) if T>>v&1]
    features=[mask(vs) for vs in combinations(pts,2)]+[T]+[1<<v for v in pts]
    terms=[(features[j-1],w) for j,w in es.items() if j]
    assert len(terms)==1
    u,w=terms[0];assert w==1 and es[0]=={2:3,3:1}[u.bit_count()]
    local.append((T,u,w,es[0]))
H=sum(w*rhs for w,rhs,*_ in rows)+sum(rhs for *_,rhs in local)
assert H==48
def coefficient(S):
    q=0
    for w,rhs,kind,a,u in rows:
        if kind=='incidence':q+=w*int(S&a==a)
        elif kind=='exact':q+=w*int(S&a==u)
        else:q+=int(bool(S&(1<<a)) and not(S.bit_count()==4 and S&Y==S))
    q+=sum(w for A,u,w,rhs in local if S&A==u)
    return q
admissible=[];excluded=[]
for k in range(5):
    for vs in combinations(range(12),k):
        S=mask(vs)
        internal=k==4 and (S&Y==S or S&Z==S)
        if (internal and S!=M) or any(S&T==S&M==T&M for T in LINK):
            excluded.append(S);continue
        q=coefficient(S)
        assert q>=int(S!=M),(vs,q)
        admissible.append([S,q])
assert coefficient(M)==0
# The stabilizer exchanges the two covering vertices1 and3 of M.
aut=[p for p in permutations(range(6)) if {mask(p[v] for v in range(6) if T>>v&1) for T in D}==set(D)]
swap=next(p for p in aut if p[1]==3 and p[3]==1 and {p[v] for v in range(4)}==set(range(4)))
out={'result':'PASS','trace_domain':794,'admissible_count':len(admissible),'excluded_count':len(excluded),
     'H':H,'marker_coefficient':0,'inequality':'r-1 <=48; if r=49, the positive C5:3 row is tight, hence d3=16',
     'transported_equality':'stabilizer gives d1=16 as well','stabilizer_permutation':list(swap),
     'rows':rows,'local_rows':local,'admissible':admissible,
     'source_receipt_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),
     'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'assurance':'certificate-diagnostic; ordinary weighted-sum/equality interpretation; no Lean'}
(P/'degree19/Ysingle-equality-check.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: r<=49; r=49 forces d1=d3=16. Stabilizer:',swap)
