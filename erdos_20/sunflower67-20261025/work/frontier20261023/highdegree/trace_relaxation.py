#!/usr/bin/env python3
"""Support-independent necessary projection for a degree-20 star in SF4.

Discovery only. No old mu42 singleton/minimum-degree/support assumptions.
Counts are exact traces on the 12 link points plus any marked exterior point.
LP/MILP infeasibility is not a proof certificate until independently checked.
"""
import argparse, hashlib, itertools as it, json, pathlib, time
import numpy as np
from scipy.optimize import linprog, milp, Bounds, LinearConstraint
from scipy.sparse import coo_matrix

ROOT = pathlib.Path(__file__).resolve().parent
mask = lambda xs: sum(1 << i for i in xs)
D = tuple(mask(map(int,s)) for s in '012 015 023 034 045 124 134 135 235 245'.split())
LINK = D + tuple(t << 6 for t in D)
X = 1 << 13
STAR = tuple(t | X for t in LINK)
MARKERS = {'none':None, 'I00':mask((0,1,2,3)),
           'E00':mask((0,1,2,6)), 'E01':mask((0,1,2,12)),
           'E02':mask((0,1,3,6)), 'E03':mask((0,1,3,12)),
           'E04':mask((0,1,6,7)), 'E05':mask((0,1,6,12))}

def build(case='none', n_family=68):
    M=MARKERS[case]; n=13 if M is not None and M>>12 else 12
    traces=tuple(mask(s) for size in range(5) for s in it.combinations(range(n),size))
    index={s:i for i,s in enumerate(traces)}; m=len(traces)
    target=n_family-20
    low=[0]*m; high=[{0:target,1:20,2:6,3:2,4:1}[s.bit_count()] for s in traces]
    if M is not None:
        low[index[M]]=1
        for i,s in enumerate(traces):
            if any(s&t == s&M == t&M for t in LINK): high[i]=0
    rows=[]
    def put(label,cs,rhs):rows.append((label,{i:int(v) for i,v in cs.items() if v},int(rhs)))
    # Incidence caps count fixed star members and the same projected residuals.
    for size,cap in [(1,20),(2,6),(3,2)]:
        for vs in it.combinations(range(n),size):
            a=mask(vs)
            put(f'incidence:{a}',{i:1 for i,s in enumerate(traces) if s&a==a},
                cap-sum(t&a==a for t in LINK))
    # All actual marked anchors have their exact nonempty trace capacities.
    anchors=STAR+((M,) if M is not None else ())
    for a in anchors:
        put(f'disjoint:{a}',{i:1 for i,s in enumerate(traces) if not s&a},
            27-sum(not t&a for t in STAR))
        points=[v for v in range(14) if a>>v&1]
        for size,cap in [(1,10),(2,3),(3,1)]:
            for vs in it.combinations(points,size):
                u=mask(vs)
                put(f'exact:{a}:{u}',{i:1 for i,s in enumerate(traces) if s&a==u},
                    cap-sum(t&a==u for t in STAR))
    # Source universal C5 obstruction: d(y)-I_y <=15. Fixed star degree is5.
    for v in range(12):
        comp=63 if v<6 else 63<<6
        put(f'C5:{v}',{i:1 for i,s in enumerate(traces)
                     if s>>v&1 and not (s.bit_count()==4 and s&comp==s)},10)
    # Source universal cooccurring pair degree sum at mu>=n_family-27.
    # It is used only in actual fixed anchors; n=68 gives19, not20.
    for a in anchors:
        points=[v for v in range(14) if a>>v&1]
        for u,v in it.combinations(points,2):
            base=sum((t>>u&1)+(t>>v&1) for t in STAR)
            put(f'pair_degree:{a}:{u}:{v}',
                {i:-((s>>u&1)+(s>>v&1)) for i,s in enumerate(traces)},base-(n_family-49))
    ii=[];jj=[];vv=[]
    for r,(_,cs,rhs) in enumerate(rows):
        for j,c in cs.items():ii.append(r);jj.append(j);vv.append(c)
    A=coo_matrix((np.asarray(vv,dtype=float),(ii,jj)),shape=(len(rows),m)).tocsr()
    b=np.array([r[2] for r in rows],float)
    return traces,rows,A,b,np.array(low,float),np.array(high,float),target

def run(case,integer=False,limit=60):
    started=time.monotonic();traces,rows,A,b,lo,hi,target=build(case)
    # The number of residuals is fixed, not inferred from an objective optimum.
    if integer:
        result=milp(np.zeros(len(traces)),integrality=np.ones(len(traces)),bounds=Bounds(lo,hi),
                    constraints=[LinearConstraint(A,-np.inf,b),
                                 LinearConstraint(np.ones((1,len(traces))),target,target)],
                    options={'time_limit':limit,'mip_rel_gap':0.0})
    else:
        result=linprog(np.zeros(len(traces)),A_ub=A,b_ub=b,A_eq=np.ones((1,len(traces))),
                       b_eq=[target],bounds=list(zip(lo,hi)),method='highs',
                       options={'time_limit':limit})
    out={'case':case,'domain':'arbitrary ambient support; exact traces on12/13 fixed points',
         'assurance':'certificate-diagnostic; no exact dual certificate or Lean replay',
         'integer':integer,'status':int(result.status),'message':result.message,
         'columns':len(traces),'rows':len(rows),'seconds':time.monotonic()-started,
         'source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
    if result.x is not None:
        out['nonzero']=[[s,float(v)] for s,v in zip(traces,result.x) if abs(v)>1e-7]
        out['max_constraint_residual']=float(np.max(A@result.x-b))
        out['sum']=float(sum(result.x))
    ROOT.mkdir(exist_ok=True)
    suffix='milp' if integer else 'lp'
    (ROOT/f'{case}-{suffix}.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='nonzero'}),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--integer',action='store_true')
    ap.add_argument('--case',choices=list(MARKERS));ap.add_argument('--seconds',type=int,default=60)
    a=ap.parse_args()
    for case in ([a.case] if a.case else MARKERS):run(case,a.integer,a.seconds)
