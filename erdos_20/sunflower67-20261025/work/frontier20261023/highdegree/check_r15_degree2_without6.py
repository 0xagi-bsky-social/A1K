#!/usr/bin/env python3
"""Complete six-extension diagnostic for the second degree-two motif.

Independent generation of its 78 normalized motifs. Each allowed new triple
has at most one exterior point; its core pair has total remaining capacity
at most three over all types. Hence three new labels cover an ENTIRE completion,
not just one tested triple. Actual normalization proof is recorded separately.
"""
import argparse
import hashlib
import itertools as it
import json
import time
from pathlib import Path


def sf(a,b,c):
    return a & b == a & c == b & c


def witness(fam):
    for a,b,c in it.combinations(fam,3):
        if sf(a,b,c):
            return {'kind':'sunflower','members':[sorted(a),sorted(b),sorted(c)]}
    for a in fam:
        ds=[b for b in fam if not a&b]
        if len(ds)>6:
            return {'kind':'rho','anchor':sorted(a),'disjoint':[sorted(b) for b in ds[:7]]}
    return None


def search(fam,candidates,deadline):
    nodes=0
    completions=[]
    rejection_counts={'cardinality':0,'sunflower':0,'rho':0,'pair_capacity':0}
    def dfs(chosen,pool):
        nonlocal nodes
        nodes+=1
        if nodes%128==0 and time.monotonic()>deadline:
            raise TimeoutError('bounded extension search exceeded10s')
        if len(chosen)==6:
            completions.append([sorted(t) for t in chosen])
            return
        if len(pool)<6-len(chosen):
            rejection_counts['cardinality']+=1
            return
        current=fam+chosen
        for index,c in enumerate(pool):
            if len(pool)-index<6-len(chosen):
                break
            # All pair capacities are necessary and cheaply checked.
            if any(sum(p<=a for a in current)>=2 for p in map(frozenset,it.combinations(c,2))):
                rejection_counts['pair_capacity']+=1
                continue
            if any(sf(a,b,c) for a,b in it.combinations(current,2)):
                rejection_counts['sunflower']+=1
                continue
            new=current+[c]
            if any(sum(not a&b for b in new)>6 for a in new):
                rejection_counts['rho']+=1
                continue
            dfs(chosen+[c],pool[index+1:])
    dfs([],candidates)
    return {'nodes':nodes,'completions':completions,'rejections':rejection_counts}


def run():
    start=time.monotonic()
    rows=[]
    total_nodes=0
    for common in range(4):
        d=frozenset((4,5,6))
        e=frozenset(list(range(4,4+common))+list(range(7,10-common)))
        old=set((3,))|d|e
        fresh=max(old)+1
        for uv0 in it.combinations(sorted(old)+list(range(fresh,fresh+2)),2):
            uv=frozenset(uv0)
            if sorted(uv-old)!=list(range(fresh,fresh+len(uv-old))):
                continue
            fam=[frozenset((0,1,2)),frozenset((1,2,3)),uv|{0}]
            fam += [frozenset(p)|{1} for p in it.combinations(sorted(d),2)]
            fam += [frozenset(p)|{2} for p in it.combinations(sorted(e),2)]
            why=witness(fam)
            row={'D':sorted(d),'E':sorted(e),'uv':sorted(uv),'motif':list(map(sorted,fam)),'rejection':why}
            if why is None:
                supp=set().union(*fam)
                next_point=max(supp)+1
                newpoints=set(range(next_point,next_point+3))
                universe=(supp-{0,1,2})|newpoints
                candidates=[]
                rejected=[]
                for c0 in it.combinations(sorted(universe),3):
                    c=frozenset(c0)
                    why_c=witness(fam+[c])
                    if why_c is None: candidates.append(c)
                    else: rejected.append({'candidate':list(c0),'witness':why_c})
                exterior=[c for c in candidates if c & newpoints]
                if any(len(c&newpoints)!=1 for c in exterior):
                    raise ValueError('uncontrolled multiple exterior points')
                pairs={c-newpoints for c in exterior}
                pair_caps={tuple(sorted(p)):2-sum(p<=a for a in fam) for p in pairs}
                budget=sum(pair_caps.values())
                if budget>3 or any(v<0 for v in pair_caps.values()):
                    raise ValueError('whole-completion exterior budget not proved')
                result=search(fam,candidates,start+10)
                total_nodes+=result['nodes']
                row.update(allowed_next=list(map(sorted,candidates)),rejected_next=rejected,
                           exterior_pairs=[{'pair':list(p),'capacity':cap} for p,cap in sorted(pair_caps.items())],
                           whole_completion_exterior_budget=budget,search=result)
            rows.append(row)
    count=sum(len(r.get('search',{}).get('completions',[])) for r in rows)
    return {'schema':'r15-degree2-without6-complete-v1','status':'PASS' if count==0 else 'OPEN',
            'normalized_motifs':len(rows),'admissible_partial_motifs':sum(r['rejection'] is None for r in rows),
            'search_nodes':total_nodes,'completions':count,'rows':rows,
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'seconds':time.monotonic()-start,
            'assurance':'certificate-diagnostic; ordinary arbitrary-support bridge required; not Lean.'}


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    result=run()
    with args.output.open('x') as out:json.dump(result,out,indent=2)
    print(json.dumps({k:v for k,v in result.items() if k!='rows'}))
    if result['status']!='PASS':raise SystemExit(2)
