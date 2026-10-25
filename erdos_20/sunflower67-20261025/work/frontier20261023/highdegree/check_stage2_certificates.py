#!/usr/bin/env python3
"""Exact support-independent stage-two coefficient checks, standard library only.

No solver or imported signature catalogue. Each local row is justified by a
simple explicit type, then all projected traces are covered. Ordinary geometry
proving those types is kept in stage2-proof.md; this is not Lean replay.
"""
import json, hashlib, time
from pathlib import Path
from itertools import combinations, product, permutations
from collections import Counter

P=Path(__file__).resolve().parent
t0=time.monotonic()
mask=lambda vs:sum(1<<v for v in vs)
Y=63;Z=63<<6;X=1<<13
D=tuple(mask(map(int,t)) for t in '012 015 023 034 045 124 134 135 235 245'.split())
LINK=D+tuple(t<<6 for t in D)
STAR=tuple(X|t for t in LINK)
data=json.loads((P/'stage2-certificates.json').read_text())

def verify_local(row,M):
    A=row['anchor'];terms=row['terms'];right=row['rhs']
    assert A in LINK
    if all(u.bit_count()==1 and w>0 for u,w in terms):
        # A marked pair/triple through this vertex forces its central k>=6,
        # whereas a large singleton would force k=5 after internal removal.
        for u,w in terms:
            assert u&A==u and M&A&u==u and (M&A).bit_count()>=2
        assert right==7*sum(w for _,w in terms)
        return 'marker-forces-singleton-at-most-seven'
    if len(terms)==1 and terms[0][0].bit_count() in (2,3):
        u,w=terms[0];assert u&A==u and w>0
        assert right==w*{2:3,3:1}[u.bit_count()]
        return 'universal-exact-trace-capacity'
    # The sole mixed-sign row is equivalent to c+s <=9(a+e).
    assert A==mask((6,7,8)) and right==0
    assert sorted(terms)==sorted([[mask((6,7)),-9],[mask((7,8)),1],
                                 [A,-9],[mask((7,)),1]])
    assert M&A==mask((6,7))
    # a>=1 from M, and a+c+e+s<=10 from d(7)<=15. Independently
    # enumerate only this elementary finite arithmetic interface.
    for a,c,e,s in product(range(4),range(4),range(2),range(11)):
        if a>=1 and a+c+e+s<=10:assert c+s-9*(a+e)<=0
    return 'degree-cap-and-present-pair'

def verify_row(row,M):
    parts=row['label'].split(':');kind=parts[0];w=row['weight'];rhs=row['bound']
    assert w>=0
    if kind=='incidence':
        u=int(parts[1]);cap={1:20,2:6,3:2}[u.bit_count()]
        assert rhs==cap-sum(t&u==u for t in LINK)
        return lambda s:int(s&u==u)
    if kind=='exact':
        A,u=map(int,parts[1:]);assert A in STAR+(M,) and u&A==u
        cap={1:10,2:3,3:1}[u.bit_count()]
        assert rhs==cap-sum(t&A==u for t in STAR)
        return lambda s:int(s&A==u)
    assert kind=='C5'
    v=int(parts[1]);assert 0<=v<12 and rhs==10
    return lambda s:int(bool(s&(1<<v)))

records={}
for case,C in data.items():
    M=C['marker'];scale=C['scale'];n=13 if M&(1<<12) else 12
    ev=[(r['weight'],verify_row(r,M)) for r in C['rows']]
    local_kinds=[verify_local(r,M) for r in C['local']]
    H=sum(r['weight']*r['bound'] for r in C['rows'])+sum(r['rhs'] for r in C['local'])
    def coeff(S):
        return sum(w*f(S) for w,f in ev)+sum(w for r in C['local'] for u,w in r['terms'] if S&r['anchor']==u)
    hist=Counter();excluded=0;count=0
    for k in range(5):
        for vs in combinations(range(n),k):
            S=mask(vs);count+=1
            internal=k==4 and (S&Y==S or S&Z==S)
            blocked=any(S&T==S&M==T&M for T in LINK)
            if internal or blocked:excluded+=1;continue
            q=coeff(S);assert q>=scale,(case,S,q,scale)
            hist[q]+=1
    qM=coeff(M);assert qM>=scale
    numerator=H-(qM-scale)
    assert numerator<48*scale
    records[case]={'trace_domain':count,'excluded':excluded,'admissible':count-excluded,
                   'scale':scale,'weighted_rhs':H,'marker_coefficient':qM,
                   'upper_numerator':numerator,'upper_denominator':scale,
                   'integer_residual_cap':numerator//scale,'histogram':dict(sorted(hist.items())),
                   'local_row_kinds':local_kinds}

# All non-internal four-sets using at least three link points have one of
# the six marker types. Verify the local orbit types independently by all
# 720 component permutations; arbitrary outside labels transport freely.
aut=[p for p in permutations(range(6)) if {mask(p[v] for v in range(6) if t>>v&1) for t in D}==set(D)]
def signature(S,offset):
    return min(mask(p[v] for v in range(6) if S>>(v+offset)&1) for p in aut)
def key(S):
    a,b=signature(S,0),signature(S,6)
    return tuple(sorted((a,b)))+(int(bool(S&(1<<12))),)
types={key(C['marker']):case for case,C in data.items()}
assert len(types)==6
covered=Counter()
for k in (3,4):
    for vs in combinations(range(12),k):
        S=mask(vs)|(1<<12 if k==3 else 0)
        if S.bit_count()==4 and (S&Y==S or S&Z==S):continue
        assert key(S) in types,S
        covered[types[key(S)]]+=1
assert sum(covered.values())==685
out={'result':'PASS','assurance':'certificate-diagnostic; all row-type geometric premises stated in ordinary proof',
     'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     'data_sha256':hashlib.sha256((P/'stage2-certificates.json').read_bytes()).hexdigest(),
     'records':records,'component_automorphisms':len(aut),'orbit_counts_with_one_canonical_exterior':dict(covered),
     'seconds':time.monotonic()-t0}
(P/'stage2-check.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v['integer_residual_cap'] for k,v in records.items()}))
print('All six exact coefficient covers and six orbit types PASS.')
