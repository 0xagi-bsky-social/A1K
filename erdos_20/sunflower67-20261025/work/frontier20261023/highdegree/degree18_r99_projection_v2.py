#!/usr/bin/env python3
"""Discovery-only arbitrary-support P9+P9 projection at |F|=68.

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
LINK=D[1:]+tuple(t<<6 for t in D[1:]);X=1<<13;STAR=tuple(X|t for t in LINK)
P5={0,1,2,6,7,8}
COVER={0:mask((3,5)),1:mask((4,5)),2:mask((3,4)),6:mask((9,11)),7:mask((10,11)),8:mask((9,10))}
def automorphisms():
    f=set(D[1:]);return [p for p in it.permutations(range(6)) if {mask(p[v] for v in range(6) if t>>v&1) for t in f}==f]
def move(s,p):return mask(p[v] for v in range(len(p)) if s>>v&1)
autos=automorphisms()
group=[p+tuple(v+6 for v in q)+(12,) for p,q in it.product(autos,repeat=2)]
group += [tuple(v+6 for v in p)+q+(12,) for p,q in it.product(autos,repeat=2)]
MARKERS={'none':None}
# Every internal four-set is symmetric to one of four P9 types.
for i,q in enumerate(((6,7,8,9),(6,7,9,10),(6,7,9,11),(6,9,10,11)),1):MARKERS[f'I{i:02}']=mask(q)
target={mask(t) for t in it.combinations(range(12),4) if len(set(t)&set(range(6))) not in (0,4)}
target|={mask(t)|(1<<12) for t in it.combinations(range(12),3)}
EXTERNAL_ORBITS={}
while target:
    m=min(target);orb={move(m,p) for p in group};target-=orb
    name=f'E{len(EXTERNAL_ORBITS):02}';MARKERS[name]=m;EXTERNAL_ORBITS[name]=sorted(orb)

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
            assert sx+ks[0]==18
            cs=[tuple(s for s in L.local_s_candidates(i,p,t,17,0,0) if s+ks[i]<=18) for i in (1,2,3)]
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
                    # A complete C5 point-link at total degree>=16 lies in
                    # one separated intersecting component (R16/Q8 exceptions
                    # cannot contain this complete C5). Its central k is
                    # bounded by 5+I even for a singleton smaller than8.
                    large_or_c5high=s[i]>=8 or (v not in P5 and ds[i]>=16)
                    need=max(0,ks[i]-b) if large_or_c5high else 0
                    if v in P5:
                        need=max(need,{17:1,18:4,19:5}.get(ds[i],0))
                    else:need=max(need,ds[i]-15)
                    cc.append(need)
                out.append(q+(e,)+u);cost.append(cc)
    return np.array(out,dtype=np.int16),np.array(cost,dtype=np.int16)

def build(case,empty='none',assigned=None,forbidden=()):
    M=MARKERS[case];n=13 if M is not None and M>>12 else 12
    traces=tuple(mask(vs) for k in range(5) for vs in it.combinations(range(n),k));index={s:i for i,s in enumerate(traces)}
    N=len(traces);lo=np.zeros(N);hi=np.array([{0:50,1:18,2:6,3:2,4:1}[s.bit_count()] for s in traces],float)
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
        if s in forbidden:hi[i]=0
    for M1 in selected:
        lo[index[M1]]=1
        for i,s in enumerate(traces):
            if any(s&T==s&M1==T&M1 for T in LINK):hi[i]=0
    if np.any(lo>hi):raise ValueError('conflicting selected/forbidden traces')
    bounds=list(zip(lo,hi));ub=[];eq=[];labels=[]
    def put(label,cs,rhs):ub.append(({i:int(v) for i,v in cs.items() if v},int(rhs)));labels.append(label)
    for k,cap in [(1,18),(2,6),(3,2)]:
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
    for comp in (63,63<<6):
        pool={i:1 for i,s in enumerate(traces) if (s&comp).bit_count()==1}
        put(('H27-pool',comp),pool,27)
        pts=[v for v in range(12) if comp>>v&1]
        for y,z in it.combinations(pts,2):
            put(('HP16',y,z),{i:1 for i,s in enumerate(traces) if s&comp in (1<<y,1<<z)},16)
        for y in pts:
            put(('pool-affine',comp,y),{i:2+(7 if s&comp==1<<y else 0) for i,s in enumerate(traces) if i in pool},110)
        for y in range(12):
            if not comp>>y&1:continue
            for ex in ([None] if y not in P5 else [v for v in range(12) if COVER[y]>>v&1]):
                ids=[i for i,s in enumerate(traces) if (s&comp).bit_count()==2 and s>>y&1 and (ex is None or not s>>ex&1)]
                put(('pair-pool',y,ex),{i:1 for i in ids},6)
                cs={i:9 for i in ids};cs.update({i:5 for i,s in enumerate(traces) if s&comp==1<<y})
                put(('pair-singleton',y,ex),cs,59)
    internal={}
    for v in range(12):
        comp=63 if v<6 else 63<<6
        ids=[i for i,s in enumerate(traces) if s>>v&1 and s.bit_count()==4 and s&comp==s];internal[v]=ids
        if v not in P5:
            put(('C5',v),{i:1 for i,s in enumerate(traces) if s>>v&1 and i not in ids},15-sum(T>>v&1 for T in LINK))
        else:
            # New universal deletion lemma: d(v)-I_v+J_v<=16, where J_v
            # counts internals using the unique two-cover of the P5.
            removable=[i for i in ids if traces[i]&COVER[v]!=COVER[v]]
            put(('P5-refined',v),{i:1 for i,s in enumerate(traces) if s>>v&1 and i not in removable},16-sum(T>>v&1 for T in LINK))
    degree_selectors={}
    for v in range(12):
        fixed=sum(T>>v&1 for T in LINK)
        ds=range(fixed,19);cols=list(range(len(bounds),len(bounds)+len(ds)))
        bounds.extend([(0,1)]*len(cols));degree_selectors[v]=dict(zip(ds,cols))
        eq.append(({j:1 for j in cols},1))
        cs={i:1 for i,s in enumerate(traces) if s>>v&1}
        cs.update({j:-d for d,j in degree_selectors[v].items()});eq.append((cs,-fixed))
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
            comp=63 if v<6 else 63<<6
            fixed=sum(B>>v&1 for B in STAR)
            pair_inc=[j for j,u in enumerate(feats[:3]) if u>>v&1]
            ks=[fixed+sum(int(row[j]) for j in pair_inc)+int(row[3]) for row in live]
            ds=[k+int(row[4+f]) for k,row in zip(ks,live)]
            for d,jd in degree_selectors[v].items():
                cs={jd:-1};cs.update({j:1 for j,dj in zip(cols,ds) if dj==d});eq.append((cs,0))
            lower={8:6,9:9,10:10}
            costs=[int(row[4+f]) if d>=17 or (v not in P5 and d>=16) or (int(row[4+f])>=8 and k>=8)
                   else lower.get(int(row[4+f]),0) for row,k,d in zip(live,ks,ds)]
            cs={i:-1 for i,s in enumerate(traces) if s&comp==1<<v}
            cs.update({j:c for j,c in zip(cols,costs) if c});put(('whole-pool',T,v),cs,0)
            cs={i:1 for i,s in enumerate(traces) if (s&comp).bit_count()==1}
            cs.update({j:({9:5,10:7}.get(int(row[4+f]),0)) for j,row in zip(cols,live) if row[4+f]>=9})
            put(('pool-conditional',T,v),cs,27)
            cs={i:-1 for i in internal[v]};cs.update({j:int(w) for j,w in zip(cols,ccost[:,f]) if w})
            put(('internal-cost',T,v),cs,0)
            if v in P5:
                # For a large singleton, k_v<=6+I_v-J_v.
                A=T|X
                fixed=sum(B>>v&1 for B in STAR)
                pair_inc=[j for j,u in enumerate(feats[:3]) if u>>v&1]
                geo=[]
                for row in live:
                    k=fixed+sum(int(row[j]) for j in pair_inc)+int(row[3])
                    geo.append(max(0,k-6) if row[4+f]>=8 else 0)
                cs={i:-1 for i in internal[v] if traces[i]&COVER[v]!=COVER[v]}
                cs.update({j:g for j,g in zip(cols,geo) if g})
                put(('internal-cover-cost',T,v),cs,0)
    def matrix(rows):
        rr=[];cc=[];vv=[]
        for i,(cs,_) in enumerate(rows):
            for j,v in cs.items():rr.append(i);cc.append(j);vv.append(v)
        return coo_matrix((vv,(rr,cc)),shape=(len(rows),len(bounds)),dtype=float).tocsr(),np.array([rhs for _,rhs in rows],float)
    A,b=matrix(ub);E,f=matrix(eq)
    return traces,bounds,A,b,E,f,labels,sizes

def run(case,empty='none',seconds=30,assigned=None,label=None,forbidden=()):
    start=time.monotonic();tr,bounds,A,b,E,f,labels,sizes=build(case,empty,assigned,forbidden);N=len(tr)
    print(json.dumps({'phase':'built','case':case,'empty':empty,'columns':len(bounds),'rows':len(b),'catalogue_sizes':sizes,'seconds':time.monotonic()-start}),flush=True)
    c=np.zeros(len(bounds));c[:N]=-1
    result=linprog(c,A_ub=A,b_ub=b,A_eq=E,b_eq=f,bounds=bounds,method='highs',options={'time_limit':seconds})
    rec={'case':case,'empty':empty,'assigned':assigned,'forbidden':list(forbidden),'status':int(result.status),'message':result.message,'columns':len(bounds),
         'seconds':time.monotonic()-start,'target_residuals':50,'mu':41,'point_cap':18,
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
        rec['dual']={'scale':scale,'H':H,'correction':corr,'upper_numerator':H+corr,'display':(H+corr)/scale,'below50':H+corr<50*scale,
                     'ineq':[[i,w,labels[i]] for i,w in enumerate(ys) if w],'eq':[[i,w] for i,w in enumerate(es) if w]}
        rec['primal_trace']=[[s,float(v)] for s,v in zip(tr,result.x[:N]) if v>1e-7]
    out=HERE/'degree18_r99';out.mkdir(exist_ok=True)
    (out/((label or case)+'-'+empty+'.json')).write_text(json.dumps(rec,indent=2)+'\n')
    print(json.dumps({k:v for k,v in rec.items() if k not in ('dual','primal_trace','forbidden')}),flush=True)
    if 'dual'in rec:print('Exact-box upper:',rec['dual']['display'],'below50:',rec['dual']['below50'],flush=True)
    return rec

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--case',default='I01',choices=MARKERS);ap.add_argument('--empty',default='none',choices=['none','Y','Z','both']);ap.add_argument('--seconds',type=int,default=30)
    args=ap.parse_args();run(args.case,args.empty,args.seconds)
