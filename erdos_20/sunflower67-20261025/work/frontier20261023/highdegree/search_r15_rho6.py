#!/usr/bin/env python3
"""Bounded exact search/proof-tree producer for size15,rho<=6 on eleven points.

Three complete normalized point-stars; fixed support11 is a PROVED reduction
conditional on R15-rho6-degree2-support-reduction.md, not an assumed cutoff.
No optimizer. A generated tree requires separate replay before use as evidence.
"""
import argparse
import gzip
import hashlib
import itertools as it
import json
import time
from pathlib import Path


def sf(a,b,c):
    return not ((a&b&~c)|(a&c&~b)|(b&c&~a))


def bits(mask):
    while mask:
        bit=mask&-mask
        yield bit.bit_length()-1
        mask^=bit


class Limit(Exception):pass


def search(kind,seconds,max_nodes):
    start=time.monotonic(); deadline=start+seconds
    n=11
    if kind=='two_triangles':
        cap=6; edges=list(it.combinations((1,2,3),2))+list(it.combinations((4,5,6),2))
    elif kind=='cycle5':
        cap=5; edges=[(1,2),(2,3),(3,4),(4,5),(1,5)]
    else:
        cap=5; edges=[(1,2),(1,3),(2,3),(4,5),(4,6)]
    seed=[1|(1<<a)|(1<<b) for a,b in edges]
    points=list(it.combinations(range(1,n),3))
    sets=[sum(1<<v for v in p) for p in points]; m=len(sets)
    initial_conflict=[0]*m
    triple_conflict=[[0]*m for _ in range(m)]
    disjoint=[[not a&b for b in sets] for a in sets]
    for i,j in it.combinations(range(m),2):
        if any(sf(sets[i],sets[j],a) for a in seed):
            initial_conflict[i]|=1<<j; initial_conflict[j]|=1<<i
    for i,j,k in it.combinations(range(m),3):
        if sf(sets[i],sets[j],sets[k]):
            triple_conflict[i][j]|=1<<k; triple_conflict[j][i]|=1<<k
            triple_conflict[i][k]|=1<<j; triple_conflict[k][i]|=1<<j
            triple_conflict[j][k]|=1<<i; triple_conflict[k][j]|=1<<i
    records=[]; found=None
    stats={'count':0,'min':0,'colour':0,'branch':0,'solution':0}
    def visit(chosen,pool):
        nonlocal found
        if len(records)>=max_nodes or time.monotonic()>deadline:
            raise Limit('node or wall-clock ceiling reached')
        node=len(records);rec={};records.append(rec)
        fam=seed+[sets[i] for i in chosen]
        deg=[sum(bool(a&(1<<v)) for a in fam) for v in range(n)]
        ds=[sum(not a&b for b in fam) for a in fam]
        good=0
        for i in bits(pool):
            if any(deg[v]>=cap for v in points[i]):continue
            dis=[j for j,b in enumerate(fam) if not sets[i]&b]
            if len(dis)>6 or any(ds[j]>=6 for j in dis):continue
            good|=1<<i
        pool=good;need=15-len(fam)
        if need==0:
            if any(0<d<3 for d in deg):
                rec.update(end='min',v=next(v for v,d in enumerate(deg) if 0<d<3));stats['min']+=1
                return node
            found=fam;rec['end']='solution';stats['solution']+=1
            raise Limit('actual normalized family found')
        if pool.bit_count()<need:
            rec['end']='count';stats['count']+=1;return node
        for v,d in enumerate(deg):
            if 0<d<3 and d+sum(bool(sets[i]&(1<<v)) for i in bits(pool))<3:
                rec.update(end='min',v=v);stats['min']+=1;return node
        conflict={}
        for i in bits(pool):
            blocked=initial_conflict[i]
            for j in chosen:blocked|=triple_conflict[i][j]
            conflict[i]=blocked
        # Each class is pairwise incompatible in the presence of an actual
        # selected/seed triple. A valid extension takes at most one per class.
        classes=[];unassigned=pool
        while unassigned:
            available=unassigned;cl=[]
            while available:
                i=max(bits(available),key=lambda z:(conflict[z]&available).bit_count())
                cl.append(i);unassigned&=~(1<<i);available&=conflict[i]
                available&=unassigned
            classes.append(cl)
        rec['classes']=classes
        if len(classes)<need:
            rec['end']='colour';stats['colour']+=1;return node
        stats['branch']+=1;rec['children']=[]
        for cl in reversed(classes[need-1:]):
            for i in reversed(cl):
                pool&=~(1<<i)
                child=visit(chosen+[i],pool&~conflict[i])
                rec['children'].append(child)
        return node
    status='EXHAUSTED';error=None
    try:visit([], (1<<m)-1)
    except Limit as ex:
        status='WITNESS' if found is not None else 'INCOMPLETE';error=str(ex)
    return {'schema':'r15-rho6-tree-v1','status':status,'kind':kind,'n':n,'degree_cap':cap,
            'target':15,'disjoint_cap':6,'minimum_used_degree':3,'seed':seed,
            'candidate_order':sets,'nodes':records,'counts':stats,'witness':found,
            'seconds':time.monotonic()-start,'error':error,
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'assurance':'Exact-search producer. EXHAUSTED requires independent proof-tree replay; WITNESS requires literal checking.'}


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--kind',choices=('two_triangles','cycle5','triangle_path'),required=True)
    ap.add_argument('--seconds',type=float,default=20)
    ap.add_argument('--nodes',type=int,default=100000)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    if not 0<args.seconds<=30 or not 0<args.nodes<=200000:
        raise SystemExit('bounded run requires seconds<=30,nodes<=200000')
    result=search(args.kind,args.seconds,args.nodes)
    with args.output.open('xb') as out:out.write(gzip.compress(json.dumps(result,separators=(',',':')).encode(),mtime=0))
    print(json.dumps({k:v for k,v in result.items() if k not in ('nodes','candidate_order')}))
