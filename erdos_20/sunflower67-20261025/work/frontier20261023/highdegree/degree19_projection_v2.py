#!/usr/bin/env python3
"""Discovery-only arbitrary-support P10+P9 projection at |F|=68.

Universal local signatures and conditional internal costs are imported ordinary
premises. Numerical infeasibility is not a Lean proof. No mu42/minimum-degree/
finite-exterior-universe assumption is used. Each case writes a durable receipt.
"""
import sys
sys.dont_write_bytecode=True
import itertools as it, pathlib, time, json, hashlib, argparse
from functools import lru_cache
import numpy as np
from scipy.sparse import coo_matrix
from scipy.optimize import linprog
HERE=pathlib.Path(__file__).resolve().parent
SOURCE=HERE.parents[1]/'frontier20261020/prior-art68/repository/companion/upstream'
sys.path.insert(0,str(SOURCE/'MU42/scripts'))
import local43 as L
mask=lambda vs:sum(1<<v for v in vs)
D=tuple(mask(map(int,s)) for s in '012 015 023 034 045 124 134 135 235 245'.split())
LINK=D+tuple(t<<6 for t in D[1:]);X=1<<13;STAR=tuple(X|t for t in LINK)
P5={6,7,8}
catalogue=json.loads((SOURCE/'D19/data/ORBIT_CATALOGUE.json').read_text())
MARKERS={r['id']:mask(r['mark']) for r in catalogue['internals']+catalogue['external']}
MARKERS['none']=None

@lru_cache(None)
def local_catalog(T):
    vs=[13]+[v for v in range(12) if T>>v&1];A=T|X
    px=tuple(sum(B&A==mask((13,v)) for B in STAR) for v in vs[1:])
    tf=tuple(sum(B&A==A^(1<<v) for B in STAR) for v in vs[1:])
    sx=sum(B&A==X for B in STAR);out=[];cost=[]
    for q in it.product(range(4),repeat=3):
        p=px+q
        for e in range(2):
            t=(e,)+tf;ks=tuple(1+sum(p[j] for j in L.INC[i])+sum(t)-t[i] for i in range(4))
            assert sx+ks[0]==19
            cs=[tuple(s for s in L.local_s_candidates(i,p,t,17,0,0) if s+ks[i]<=19) for i in (1,2,3)]
            for u in it.product(*cs):
                s=(sx,)+u;ds=tuple(a+b for a,b in zip(s,ks))
                # The prescribed codegree d(x,v)=4 excludes a P10 component
                # containing x in a high-degree P5-neighbour link.
                if any(v in P5 and ds[i]>=17 and (s[i],ks[i]) not in
                       {17:((10,7),(9,8),(8,9)),18:((10,8),(9,9)),19:((10,9),)}[ds[i]]
                       for i,v in enumerate(vs[1:],1)):continue
                if 1+sum(p)+sum(t)+sum(s)<41:continue
                if any(ds[i]+ds[j]<19 for i,j in L.PAIRS):continue
                if sum(d>=19 for d in ds)>2:continue
                if sum(p)+sum(t)>(12,14,17,19,22)[sum(a<8 for a in s)]:continue
                if not L.equality_consistent(p,t,s,ks):continue
                cc=[]
                for i,v in enumerate(vs[1:],1):
                    b=6 if v in P5 else 5
                    need=max(0,ks[i]-b) if s[i]>=8 else 0
                    if v in P5:
                        need=max(need,{17:1,18:4,19:5}.get(ds[i],0))
                    else:need=max(need,ds[i]-15)
                    cc.append(need)
                out.append(q+(e,)+u);cost.append(cc)
    return np.array(out,dtype=np.int16),np.array(cost,dtype=np.int16)

def build(case,empty='none',assigned=None):
    M=MARKERS[case];n=13 if M is not None and M>>12 else 12
    traces=tuple(mask(vs) for k in range(5) for vs in it.combinations(range(n),k));index={s:i for i,s in enumerate(traces)}
    N=len(traces);lo=np.zeros(N);hi=np.array([{0:49,1:19,2:6,3:2,4:1}[s.bit_count()] for s in traces],float)
    selected=[]
    if M is not None:selected.append(M)
    if assigned:
        for comp,chosen in assigned.items():
            C=63 if comp=='Y' else 63<<6
            for i,s in enumerate(traces):
                if s.bit_count()==4 and s&C==s:
                    hi[i]=int(s in chosen);lo[i]=int(s in chosen)
            selected.extend(chosen)
    for i,s in enumerate(traces):
        if s.bit_count()==4 and ((empty in ('Y','both') and s&63==s) or (empty in ('Z','both') and s&(63<<6)==s)):hi[i]=0
    for M1 in selected:
        lo[index[M1]]=1
        for i,s in enumerate(traces):
            if any(s&T==s&M1==T&M1 for T in LINK):hi[i]=0
    if np.any(lo>hi):raise ValueError('conflicting selected/forbidden traces')
    bounds=list(zip(lo,hi));ub=[];eq=[];labels=[]
    def put(label,cs,rhs):ub.append(({i:int(v) for i,v in cs.items() if v},int(rhs)));labels.append(label)
    for k,cap in [(1,19),(2,6),(3,2)]:
        for vs in it.combinations(range(n),k):
            u=mask(vs);put(('incidence',u),{i:1 for i,s in enumerate(traces) if s&u==u},cap-sum(T&u==u for T in LINK))
    anchors=STAR+tuple(dict.fromkeys(selected))
    for A in anchors:
        put(('disjoint',A),{i:1 for i,s in enumerate(traces) if not s&A},27-sum(not B&A for B in STAR))
        pts=[v for v in range(14) if A>>v&1]
        for k,cap in [(1,10),(2,3),(3,1)]:
            for vs in it.combinations(pts,k):
                u=mask(vs);put(('exact',A,u),{i:1 for i,s in enumerate(traces) if s&A==u},cap-sum(B&A==u for B in STAR))
        for u,v in it.combinations(pts,2):
            base=sum((B>>u&1)+(B>>v&1) for B in STAR)
            put(('pair-degree',A,u,v),{i:-((s>>u&1)+(s>>v&1)) for i,s in enumerate(traces)},base-19)
    internal={}
    for v in range(12):
        comp=63 if v<6 else 63<<6
        ids=[i for i,s in enumerate(traces) if s>>v&1 and s.bit_count()==4 and s&comp==s];internal[v]=ids
        if v not in P5:
            put(('C5',v),{i:1 for i,s in enumerate(traces) if s>>v&1 and i not in ids},15-sum(T>>v&1 for T in LINK))
        else:
            put(('P5',v),{i:1 for i,s in enumerate(traces) if s>>v&1 and i not in ids},16-sum(T>>v&1 for T in LINK))
    sizes=[]
    for T in LINK:
        cat,cost=local_catalog(T);pts=[v for v in range(12) if T>>v&1]
        feats=[mask(vs) for vs in it.combinations(pts,2)]+[T]+[1<<v for v in pts]
        buckets=[[i for i,s in enumerate(traces) if s&T==u] for u in feats]
        alive=np.ones(len(cat),bool)
        for f,ids in enumerate(buckets):alive &= (cat[:,f]>=sum(lo[ids])) & (cat[:,f]<=sum(hi[ids]))
        for j,v in enumerate(pts):alive &= cost[:,j]<=sum(hi[internal[v]])
        live=cat[alive];ccost=cost[alive];cols=list(range(len(bounds),len(bounds)+len(live)))
        sizes.append(len(cols));bounds.extend([(0,1)]*len(cols))
        eq.append(({j:1 for j in cols},1))
        for f,ids in enumerate(buckets):
            cs={i:1 for i in ids};cs.update({j:-int(w) for j,w in zip(cols,live[:,f]) if w});eq.append((cs,0))
        for f,v in enumerate(pts):
            cs={i:-1 for i in internal[v]};cs.update({j:int(w) for j,w in zip(cols,ccost[:,f]) if w})
            put(('internal-cost',T,v),cs,0)
    def matrix(rows):
        rr=[];cc=[];vv=[]
        for i,(cs,_) in enumerate(rows):
            for j,v in cs.items():rr.append(i);cc.append(j);vv.append(v)
        return coo_matrix((vv,(rr,cc)),shape=(len(rows),len(bounds)),dtype=float).tocsr(),np.array([rhs for _,rhs in rows],float)
    A,b=matrix(ub);E,f=matrix(eq)
    return traces,bounds,A,b,E,f,labels,sizes

def run(case,empty='none',seconds=30,assigned=None,label=None):
    start=time.monotonic();tr,bounds,A,b,E,f,labels,sizes=build(case,empty,assigned);N=len(tr)
    print(json.dumps({'phase':'built','case':case,'empty':empty,'columns':len(bounds),'rows':len(b),'catalogue_sizes':sizes,'seconds':time.monotonic()-start}),flush=True)
    c=np.zeros(len(bounds));c[:N]=-1
    result=linprog(c,A_ub=A,b_ub=b,A_eq=E,b_eq=f,bounds=bounds,method='highs',options={'time_limit':seconds})
    rec={'case':case,'empty':empty,'assigned':assigned,'status':int(result.status),'message':result.message,'columns':len(bounds),
         'seconds':time.monotonic()-start,'target_residuals':49,'mu':41,'point_cap':19,
         'source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
         'imported_local43_sha256':hashlib.sha256((SOURCE/'MU42/scripts/local43.py').read_bytes()).hexdigest(),
         'assurance':'certificate-diagnostic; imported universal geometry; not Lean or complete branch proof'}
    if result.status==0:
        rec['solver_upper']=-float(result.fun)
        scale=10**10;ys=[max(0,round(-v*scale)) for v in result.ineqlin.marginals];es=[round(-v*scale) for v in result.eqlin.marginals]
        q=[0]*len(bounds)
        for mat,ws in [(A,ys),(E,es)]:
            for i,w in enumerate(ws):
                if not w:continue
                for j in range(mat.indptr[i],mat.indptr[i+1]):q[int(mat.indices[j])]+=w*int(mat.data[j])
        H=sum(w*int(v) for w,v in zip(ys,b))+sum(w*int(v) for w,v in zip(es,f))
        corr=sum(max(int(l)*((scale if j<N else 0)-q[j]),int(u)*((scale if j<N else 0)-q[j])) for j,(l,u) in enumerate(bounds))
        rec['dual']={'scale':scale,'H':H,'correction':corr,'upper_numerator':H+corr,'display':(H+corr)/scale,'below49':H+corr<49*scale,
                     'ineq':[[i,w,labels[i]] for i,w in enumerate(ys) if w],'eq':[[i,w] for i,w in enumerate(es) if w]}
        rec['primal_trace']=[[s,float(v)] for s,v in zip(tr,result.x[:N]) if v>1e-7]
    out=HERE/'degree19';out.mkdir(exist_ok=True)
    (out/((label or case)+'-'+empty+'.json')).write_text(json.dumps(rec,indent=2)+'\n')
    print(json.dumps({k:v for k,v in rec.items() if k not in ('dual','primal_trace')}),flush=True)
    if 'dual'in rec:print('Exact-box upper:',rec['dual']['display'],'below49:',rec['dual']['below49'],flush=True)
    return rec

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--case',default='I01',choices=MARKERS);ap.add_argument('--empty',default='none',choices=['none','Y','Z','both']);ap.add_argument('--seconds',type=int,default=30)
    args=ap.parse_args();run(args.case,args.empty,args.seconds)
