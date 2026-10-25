#!/usr/bin/env python3
"""Couple universal mu41 anchor tables to shared support-free trace counts.

Exploratory LP only. The imported local signature routine is a prior source
dependency, not a locally proved theorem. No mu42 bootstrap is imported.
"""
import sys
sys.dont_write_bytecode=True
import itertools as it, pathlib, time, json, hashlib, argparse
import numpy as np
from scipy.sparse import coo_matrix, hstack
from scipy.optimize import linprog
import trace_relaxation as R

HERE=pathlib.Path(__file__).resolve().parent
SOURCE=HERE.parents[1]/'frontier20261020/prior-art68/repository/companion/upstream/MU42/scripts'
sys.path.insert(0,str(SOURCE))
import local43 as L

def catalog(internal_free=False):
    out=[]
    for q in it.product(range(4),repeat=3):
        p=(2,2,2)+q
        for e in range(2):
            t=(e,1,1,1)
            ks=tuple(1+sum(p[j] for j in L.INC[i])+sum(t)-t[i] for i in range(4))
            cs=[L.local_s_candidates(i,p,t,17,0,0) for i in (1,2,3)]
            for u in it.product(*cs):
                s=(10,)+u;ds=tuple(a+b for a,b in zip(s,ks))
                if internal_free:
                    if any(ds[i]>15 for i in (1,2,3)):continue
                    if any(s[i]>=8 and ks[i]!=5 for i in (1,2,3)):continue
                if 20+sum(q)+e+sum(u)<41:continue
                if any(ds[i]+ds[j]<19 for i,j in L.PAIRS):continue
                if sum(d>=19 for d in ds)>2:continue
                if sum(p)+sum(t)>(12,14,17,19,22)[sum(a<8 for a in s)]:continue
                if not L.equality_consistent(p,t,s,ks):continue
                out.append(q+(e,)+u)
    return np.array(out,dtype=np.int16)

def run(case,limit,maximize=False,internal_free=False):
    started=time.monotonic();cat=catalog(internal_free)
    traces,rows,A,b,lo,hi,target=R.build(case);n=len(traces)
    if internal_free:
        for i,s in enumerate(traces):
            if s.bit_count()==4 and (s & 63 == s or s & (63<<6) == s):hi[i]=0
        if np.any(lo>hi):raise ValueError('marker contradicts internal-free premise')
    rr=[];cc=[];vv=[];rhs=[];bounds=list(zip(lo,hi));sizes=[]
    def put(inds,vals,right):
        row=len(rhs);rhs.append(right)
        rr.append(np.full(len(inds),row,dtype=np.int32))
        cc.append(np.array(inds,dtype=np.int32));vv.append(np.array(vals,float))
    put(range(n),np.ones(n),target)
    for t in R.LINK:
        pts=[v for v in range(12) if t>>v&1]
        features=[R.mask(p) for p in it.combinations(pts,2)]+[t]+[1<<v for v in pts]
        buckets=[[i for i,s in enumerate(traces) if s&t==u] for u in features]
        # Exact 4-trace lower/upper bounds propagate into possible anchor rows.
        alive=np.ones(len(cat),bool)
        for f,ids in enumerate(buckets):
            alive &= (cat[:,f]>=sum(lo[ids])) & (cat[:,f]<=sum(hi[ids]))
        live=cat[alive];cols=np.arange(len(bounds),len(bounds)+len(live),dtype=np.int32)
        sizes.append(len(cols));bounds.extend([(0,1)]*len(cols))
        put(cols,np.ones(len(cols)),1)
        for f,ids in enumerate(buckets):
            put(np.concatenate((ids,cols)),np.concatenate((np.ones(len(ids)),-live[:,f].astype(float))),0)
    total=len(bounds)
    E=coo_matrix((np.concatenate(vv),(np.concatenate(rr),np.concatenate(cc))),shape=(len(rhs),total)).tocsr()
    AA=hstack((A,coo_matrix((A.shape[0],total-n))),format='csr')
    print(json.dumps({'phase':'built','case':case,'base_columns':n,'columns':total,'catalog':len(cat),
                      'row_columns':sizes,'elapsed':time.monotonic()-started}),flush=True)
    if maximize:
        E=E[1:];rhs=rhs[1:]
    objective=np.zeros(total)
    if maximize:objective[:n]=-1
    result=linprog(objective,A_ub=AA,b_ub=b,A_eq=E,b_eq=rhs,
                   bounds=bounds,method='highs',options={'time_limit':limit})
    rec={'case':case,'mu':41,'assurance':'certificate-diagnostic; imported signature assumptions; no exact dual proof',
         'universe':'arbitrary exterior support; shared12/13-point traces',
         'r9_minimum':0,'r10_minimum':0,'minimum_used_degree_assumed':None,
         'minimum_cooccurring_degree_sum':19,'catalog_rows':len(cat),'columns':total,
         'maximize_residuals':maximize,'status':int(result.status),'message':result.message,'seconds':time.monotonic()-started,
         'internal_free':internal_free,
         'internal_free_dependencies':'internal-proof.md; universal C5 neighbour cap15 and central large-singleton k=5' if internal_free else None,
         'source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
         'imported_source_sha256':hashlib.sha256((SOURCE/'local43.py').read_bytes()).hexdigest()}
    if result.x is not None:
        rec['trace_nonzero']=[[s,float(v)] for s,v in zip(traces,result.x[:n]) if abs(v)>1e-7]
        rec['max_inequality_residual']=float(np.max(AA@result.x-b))
        rec['max_equality_residual']=float(np.max(np.abs(E@result.x-rhs)))
    if maximize and result.status==0:
        scale=10**10
        ys=[max(0,round(-v*scale)) for v in result.ineqlin.marginals]
        es=[round(-v*scale) for v in result.eqlin.marginals]
        q=[0]*total
        for mat,weights in [(AA,ys),(E,es)]:
            for i,w in enumerate(weights):
                if not w:continue
                for j in range(mat.indptr[i],mat.indptr[i+1]):
                    coeff=mat.data[j];assert coeff==round(coeff)
                    q[int(mat.indices[j])]+=w*int(coeff)
        H=sum(w*int(v) for w,v in zip(ys,b))+sum(w*int(v) for w,v in zip(es,rhs))
        corr=sum(max(int(l)*((scale if j<n else 0)-q[j]),int(u)*((scale if j<n else 0)-q[j]))
                 for j,(l,u) in enumerate(bounds))
        rec['exact_dual']={'scale':scale,'H':H,'box_correction':corr,'upper_numerator':H+corr,
                           'target_numerator':target*scale,'strictly_below_target':H+corr<target*scale,
                           'upper_float_for_display':(H+corr)/scale,
                           'ineq_nonzero':[[i,w] for i,w in enumerate(ys) if w],
                           'eq_nonzero':[[i,w] for i,w in enumerate(es) if w]}
        rec['solver_objective_for_diagnostic']=-float(result.fun)
    suffix='coupled-max' if maximize else 'coupled'
    if internal_free:suffix='internal-free-'+suffix
    (HERE/f'{case}-{suffix}.json').write_text(json.dumps(rec,indent=2)+'\n')
    print(json.dumps({k:v for k,v in rec.items() if k!='trace_nonzero'}),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--case',default='I00',choices=R.MARKERS)
    ap.add_argument('--seconds',type=int,default=60);ap.add_argument('--maximize',action='store_true')
    ap.add_argument('--internal-free',action='store_true')
    a=ap.parse_args();run(a.case,a.seconds,a.maximize,a.internal_free)
