#!/usr/bin/env python3
"""Independent set-based replay of one bounded size15 proof tree.

No producer import or search ordering heuristic. Reconstructs all candidates,
every scalar rejection and each colour incompatibility by literal finite sets.
"""
import argparse
import copy
import gzip
import hashlib
import itertools as it
import json
import time
from collections import Counter
from pathlib import Path

SOURCE='a4f14ee8e8e24bbe3c1a6f4b5af626f72aa29b1b622a47fcbb344fd920d9bed8'


def need(ok,msg):
    if not ok:raise ValueError(msg)


def flower(a,b,c):
    return a&b == a&c == b&c


def check(tree,seconds=30):
    started=time.monotonic()
    need(tree['schema']=='r15-rho6-tree-v1' and tree['status']=='EXHAUSTED','incomplete or unknown certificate')
    need(tree['source_sha256']==SOURCE,'wrong producer identity')
    kind=tree['kind'];need(kind in ('two_triangles','cycle5','triangle_path'),'kind')
    if kind=='two_triangles':
        cap=6;edges=list(it.combinations((1,2,3),2))+list(it.combinations((4,5,6),2))
    elif kind=='cycle5':cap=5;edges=[(1,2),(2,3),(3,4),(4,5),(1,5)]
    else:cap=5;edges=[(1,2),(1,3),(2,3),(4,5),(4,6)]
    need((tree['n'],tree['degree_cap'],tree['target'],tree['disjoint_cap'],tree['minimum_used_degree'])==(11,cap,15,6,3),'literal scope changed')
    seed=tuple(frozenset((0,a,b)) for a,b in edges)
    candidates=tuple(frozenset(t) for t in it.combinations(range(1,11),3))
    need(tree['seed']==[sum(2**v for v in t) for t in seed],'seed mismatch')
    need(tree['candidate_order']==[sum(2**v for v in t) for t in candidates],'candidate coverage mismatch')
    records=tree['nodes'];visited=set();hist=Counter();colour_pairs=0
    seed_conflicts=[set() for _ in candidates]
    for i,j in it.combinations(range(len(candidates)),2):
        if any(flower(candidates[i],candidates[j],a) for a in seed):
            seed_conflicts[i].add(j);seed_conflicts[j].add(i)
    def visit(idx,chosen,pool):
        nonlocal colour_pairs
        if time.monotonic()-started>seconds:raise TimeoutError('independent replay deadline')
        need(type(idx) is int and 0<=idx<len(records) and idx not in visited,'cyclic/reused/missing node')
        visited.add(idx);rec=records[idx]
        fam=seed+tuple(candidates[i] for i in chosen)
        deg=Counter(v for a in fam for v in a)
        ds=[sum(not a&b for b in fam) for a in fam]
        valid=set()
        for i in pool:
            a=candidates[i]
            if any(deg[v]>=cap for v in a):continue
            dis=[j for j,b in enumerate(fam) if not a&b]
            if len(dis)>6 or any(ds[j]>=6 for j in dis):continue
            valid.add(i)
        pool=valid;remaining=15-len(fam)
        end=rec.get('end')
        if end=='count':
            need(len(pool)<remaining,'false cardinality leaf');hist['count']+=1;return
        if end=='min':
            v=rec['v'];need(type(v) is int and 0<=v<11,'minimum-degree vertex')
            need(0<deg[v]<3 and deg[v]+sum(v in candidates[i] for i in pool)<3,'false minimum-degree leaf')
            hist['min']+=1;return
        need(end in (None,'colour'),'solution or unknown terminal')
        classes=rec['classes'];flat=[i for cl in classes for i in cl]
        need(all(classes) and all(type(i) is int for i in flat),'empty or malformed colour class')
        need(len(flat)==len(set(flat)) and set(flat)==pool,'colour partition incomplete')
        selected=tuple(candidates[i] for i in chosen)
        def conflict(i,j):
            return j in seed_conflicts[i] or any(flower(candidates[i],candidates[j],a) for a in selected)
        for cl in classes:
            for i,j in it.combinations(cl,2):
                need(conflict(i,j),'false colour incompatibility');colour_pairs+=1
        if end=='colour':
            need(len(classes)<remaining,'false colour upper bound');hist['colour']+=1;return
        need(remaining>0 and len(classes)>=remaining,'invalid branch')
        hist['branch']+=1
        order=[i for cl in reversed(classes[remaining-1:]) for i in reversed(cl)]
        need(len(order)==len(rec['children']),'omitted branch child')
        for i,child in zip(order,rec['children']):
            pool.remove(i)
            child_pool={j for j in pool if not conflict(i,j)}
            visit(child,chosen+(i,),child_pool)
        need(pool==set(i for cl in classes[:remaining-1] for i in cl),'uncovered colour prefix')
    visit(0,(),set(range(len(candidates))))
    need(len(visited)==len(records),'unreachable records')
    expected={k:hist[k] for k in ('count','min','colour','branch','solution')}
    need(tree['counts']==expected and tree['witness'] is None,'declared counters differ')
    return {'kind':kind,'nodes':len(records),'counts':expected,'colour_pairs_checked':colour_pairs,
            'seconds':time.monotonic()-started}


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('tree',type=Path)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--negative-controls',action='store_true')
    args=ap.parse_args()
    raw=args.tree.read_bytes();tree=json.loads(gzip.decompress(raw))
    result=check(tree)
    negatives=[]
    if args.negative_controls:
        for name in ('wrong_target','omitted_child','wrong_source'):
            bad=copy.deepcopy(tree)
            if name=='wrong_target':bad['target']=16
            elif name=='wrong_source':bad['source_sha256']='0'*64
            else:
                branch=next(r for r in bad['nodes'] if 'children' in r and r['children'])
                branch['children'].pop()
            try:check(bad)
            except ValueError as e:negatives.append({'name':name,'rejected':True,'reason':str(e)})
            else:raise ValueError('negative control accepted: '+name)
    need(args.tree.read_bytes()==raw,'tree changed during replay')
    result.update(status='PASS',tree=str(args.tree.resolve()),tree_sha256=hashlib.sha256(raw).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),negative_controls=negatives,
                  assurance='Independent set-based finite proof-tree replay; conditional ordinary support reduction; not Lean.')
    with args.output.open('x') as out:json.dump(result,out,indent=2)
    print(json.dumps(result))
