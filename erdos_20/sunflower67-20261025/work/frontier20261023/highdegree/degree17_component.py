#!/usr/bin/env python3
"""D17 single P10/P9 component: discovery constructor, arbitrary exterior support.

At |F|=68, mu>=41 and global Delta<=17, use an actual degree17 root.
A P10 component leaves seven unspecified opposite link triples; a P9 leaves
eight. No I7 classification, exterior universe, mu42 premise or singleton
bootstrap is imported. r10=r9=0. The minimum used degree7 and crowding26
are the prior mu41/Delta<=18 results, not old minimum4 assumptions.

Adaptation: degree18_component.py at SHA-256 8300c77f... (full record below).
All local rows are regenerated with the new root singleton and cap. The 13
P10 / 79 P9 internal orbit families remain the same combinatorial catalogue.
Ordinary source bridge: D17-research.md and D18-R99-bridge.md.
This file was prepared without running its constructor, catalogues or solver.
Any later solver receipt is discovery plus an exact integer box diagnostic,
conditional on imported geometry; it is neither Lean nor a branch closure.
"""
import json,hashlib,time,argparse
import sys
sys.dont_write_bytecode=True
from itertools import product,combinations,permutations
from functools import lru_cache
from pathlib import Path
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[2]
PRIOR=REPO/'work/frontier20261020/prior-art68'
SOURCE=PRIOR/'repository/companion/upstream'
ROOT_DEGREE=17
POINT_CAP=17
MU=41
MIN_USED_DEGREE=7
EXPECTED_ORBITS={10:13,9:79}
ADAPTATION_SOURCE={
 'path':'work/frontier20261023/highdegree/degree18_component.py',
 'sha256':'8300c77fb1bf46c35f0028debf91b41a6ed07b035d9d324fb1239b98cc5bc557',
 'description':'D18 component source including whole-pool rows, read 2026-10-23',
}
SOURCE_COMMIT='90c03c79bcf44eb8f61dff1b86091b822cc4cd3c'
# These are imported proof/code dependencies. Fail closed on source drift;
# the adaptation source itself is recorded historically, not imported.
PINNED_DEPENDENCIES={
 'repository/companion/upstream/MU42/scripts/local43.py':'258221ffe8594e51616bdd125109d92151bfea13557f4e385ef453ab2e03152b',
 'FOUNDATION_LEDGER.md':'3658ac4e94efe4bc5240856300c79c43d1388085c2126cb926df64dd48881992',
 'analysis/mu41/mu41-analysis.md':'5b9821b942b6e782725c970332e00611eda29f238b96ca345b9c99f11f89744e',
 'replay-selected-20261020/RECEIPT.json':'930a417d5f24c10056c9b10fb436fc7e52bdb13d327ed262edb895d1fd5eae8f',
 'repository/paper/main.tex':'4aa36c9d56af5a8e3bdb44749107820549a73e0d3405e6c700104fa4c30e5c21',
 'repository/companion/terminal/cross15/results/cross16_certificate.json':'fa9e49530acf9170b073c4ed24fde9ae9eb30ff78bf1edeed2a8f21018ed839b',
 'repository/companion/terminal/cross15/src/verify.py':'f72bdb066eb40ebd3a5c072d0ed8431a547d06ae8d5581c408a44326df31422d',
}
def check_sources():
 for rel,want in PINNED_DEPENDENCIES.items():
  got=hashlib.sha256((PRIOR/rel).read_bytes()).hexdigest()
  if got!=want:raise ValueError(f'Imported source changed: {rel}: {got}')
check_sources()
sys.path.insert(0,str(SOURCE/'MU42/scripts'))
import local43 as L
P=tuple(tuple(sorted(T)) for T in L.P)
U=tuple(T for n in (1,2,3) for T in combinations(range(6),n))
QUADS=tuple(combinations(range(6),4))
def sf(A,B,C):return A&B==A&C==B&C
def degrees(r):return tuple(1+r[10+i]+sum(r[j] for j in L.INC[i])+sum(r[6:10])-r[6+i] for i in range(4))
def models(m):return P if m==10 else P[1:] if m==9 else ()
@lru_cache(None)
def raw_rows(m,k,r10,r9,T):
 M=models(m);A=frozenset(T)
 alpha=tuple(sum(frozenset(B)&A=={v} for B in M) for v in T)
 tau=tuple(sum(frozenset(B)&A==A-{v} for B in M) for v in T)
 result=[]
 for p_tail in product(range(4),repeat=3):
  p=alpha+p_tail
  for e in (0,1):
   t=(e,*tau);kk=tuple(1+sum(p[j] for j in L.INC[i])+sum(t)-t[i] for i in range(4))
   if k+kk[0]!=ROOT_DEGREE:raise ValueError('Central degree mismatch')
   if k not in L.local_s_candidates(0,p,t,17,r10,r9):continue
   options=[tuple(s for s in L.local_s_candidates(i,p,t,17,r10,r9)
                  if MIN_USED_DEGREE<=s+kk[i]<=POINT_CAP) for i in (1,2,3)]
   for tail in product(*options):
    ss=(k,*tail);ds=tuple(a+b for a,b in zip(ss,kk))
    if min(ds)<MIN_USED_DEGREE or max(ds)>POINT_CAP:continue
    if any(ds[i]+ds[j]<19 for i,j in L.PAIRS):continue
    if 1+sum(p)+sum(t)+sum(ss)<MU:continue
    # Imported crowding26 bridge: valid already at mu41 and Delta<=18.
    if sum(sorted(ss)[-3:])>26:continue
    if sum(ds)<50 or any(sum(ds)+d<59 for d in ds):continue
    if sum(p)+sum(t)>(12,14,17,19,22)[sum(s<8 for s in ss)]:continue
    if not L.equality_consistent(p,t,ss,kk):continue
    result.append(p+t+ss)
 return tuple(sorted(set(result)))

def catalog(m):
 M=models(m);fixed=[frozenset((6,*T)) for T in M];all_int=[]
 def rec(start,chosen,F):
  all_int.append(tuple(chosen))
  for i in range(start,15):
   Q=frozenset(QUADS[i])
   if any(sf(Q,A,B) for A,B in combinations(F,2)):continue
   rec(i+1,chosen+[i],F+[Q])
 rec(0,[],fixed)
 autos=[p for p in permutations(range(6)) if {tuple(sorted(p[v] for v in T)) for T in M}==set(M)]
 images=[[QUADS.index(tuple(sorted(p[v] for v in Q))) for Q in QUADS] for p in autos]
 seen=set();records=[]
 for inds in sorted(all_int,key=lambda t:(len(t),t)):
  if inds in seen:continue
  orbit={tuple(sorted(pm[j] for j in inds)) for pm in images};seen.update(orbit)
  records.append({'id':f'P{m}_{len(records):03d}','interiors':[list(QUADS[j]) for j in inds],'orbit_size':len(orbit)})
 if seen!=set(all_int):raise ValueError('Internal catalogue coverage')
 if len(records)!=EXPECTED_ORBITS[m]:raise ValueError('Internal orbit count')
 return {'component':m,'internal_count':len(all_int),'automorphism_count':len(autos),'records':records}

def build(case):
 if set(case)!={'id','component','outside','r10','r9','interiors'}:raise ValueError('case fields')
 m,k,r10,r9=(case[a] for a in ('component','outside','r10','r9'))
 if m not in (9,10) or k!=ROOT_DEGREE-m or (r10,r9)!=(0,0):raise ValueError('scope')
 M=models(m);I=tuple(frozenset(Q) for Q in case['interiors']);fixed=tuple(frozenset((6,*T)) for T in M)+I
 if len(I)!=len(set(I)) or any(len(Q)!=4 or not Q<=set(range(6)) for Q in I):raise ValueError('interior validity')
 if any(sf(A,B,C) for A,B,C in combinations(fixed,3)):raise ValueError('sunflower in fixed members')
 fy=[sum(v in T for T in M) for v in range(6)];iy=[sum(v in Q for Q in I) for v in range(6)]
 caps=[min(POINT_CAP,15+iy[v]) if fy[v]==5 else POINT_CAP for v in range(6)]
 jy=[0]*6
 # P5-delete-cover: d(v)-I_v+J_v<=16. The cover is taken from the
 # complete prescribed path, not from a guessed finite exterior support.
 for v in range(6):
  if fy[v]==4:
   path=[set(T)-{v} for T in M if v in T]
   cov=[frozenset(ab) for ab in combinations(set(range(6))-{v},2)
        if all(set(ab)&E for E in path)]
   if len(cov)!=1:raise ValueError('P5 unique two-cover')
   jy[v]=sum(v in Q and cov[0]<=Q for Q in I)
   caps[v]=min(caps[v],16+iy[v]-jy[v])
   # Universal E17: a degree17 path point needs at least one internal.
   if not iy[v]:caps[v]=min(caps[v],16)
 links=[tuple(Q-{v} for Q in fixed if v in Q) for v in range(6)]
 clean=[all(A&B for A,B in combinations(T,2)) for T in links]
 esc=[]
 for v in range(6):
  if fy[v]==5 or not clean[v]:esc.append(0);continue
  covers=[frozenset(ab) for ab in combinations(set(range(6))-{v},2) if all(set(ab)&Q for Q in links[v])]
  if len(covers)>1:raise ValueError('multiple two-covers of the spine')
  extra=0
  if covers:
   candidates=[covers[0]|{z} for z in (7,8)]
   for size in (1,2):
    for ext in combinations(candidates,size):
     FF=links[v]+ext
     if all(A&B for A,B in combinations(FF,2)) and not any(sf(A,B,C) for A,B,C in combinations(FF,3)):extra=max(extra,size)
  esc.append(extra)
 bounds=[];zero=set()
 for j,T in enumerate(U):
  S=frozenset(T);off=sum(S<=Q for Q in fixed)
  hi={1:POINT_CAP,2:6,3:2}[len(T)]-off
  bad=any(A&B==A&S==B&S for A,B in combinations(fixed,2))
  if hi<0:raise ValueError('negative residual cap')
  bounds.append((0,0 if bad else hi))
  if bad:zero.add(j)
 eq=[];ups=[]
 def put(name,terms,rhs):eq.append((name,{j:int(w) for j,w in terms.items() if w},int(rhs)))
 sels=[]
 for v in range(6):
  ds=range(max(MIN_USED_DEGREE,fy[v]+iy[v]),caps[v]+1);ids=list(range(len(bounds),len(bounds)+len(ds)))
  bounds.extend([(0,1)]*len(ids));sel=dict(zip(ds,ids));sels.append(sel)
  put(f'degree-choice:{v}',dict.fromkeys(ids,1),1)
  terms={j:1 for j,T in enumerate(U) if v in T};terms.update({j:-d for d,j in sel.items()})
  put(f'degree-tie:{v}',terms,-fy[v]-iy[v])
 # ONE-HIGH, D17-research.md section4: two high neighbours would give
 # exterior pools with total at least16, contradicting imported cross15.
 one_high={j:1 for v,sel in enumerate(sels) for d,j in sel.items()
           if d>=(16 if fy[v]==5 else 17)}
 ups.append(('component-one-high',one_high,1))
 pool={U.index((v,)):1 for v in range(6)}
 ups.append(('residual-budget',dict.fromkeys(range(len(U)),1),68-ROOT_DEGREE-len(I)))
 for y,z in combinations(range(6),2):
  ups.append((f'HP15:{y}:{z}',{U.index((y,)):1,U.index((z,)):1},15))
 for y in range(6):
  ups.append((f'pool-affine:{y}',{j:2+(7 if j==U.index((y,)) else 0) for j in pool},110))
 # Each assigned internal member is an actual H27 anchor. The unspecified
 # opposite k root cones are all disjoint from it, independently of I7 shape.
 for pos,Q in enumerate(I):
  known=k+sum(not Q&A for A in fixed)
  ups.append((f'internal-H27:{pos}',{j:1 for j,T in enumerate(U) if not Q&set(T)},27-known))
 sizes=[]; all_anchor_rows=[]
 for pos,T in enumerate(M):
  A=frozenset(T);features=[(frozenset((v,)),11+i) for i,v in enumerate(T)]
  features += [(frozenset(ab),3+i) for i,ab in enumerate(combinations(T,2))]+[(A,6)]
  buckets={V:[j for j,Q in enumerate(U) if frozenset(Q)&A==V] for V,_ in features}
  off={V:sum(Q&A==V for Q in I) for V,_ in features}
  live=[]
  for row in raw_rows(m,k,r10,r9,T):
   ds=degrees(row);okay=True
   for i,v in enumerate(T,1):
    if ds[i]>caps[v]:okay=False;break
    ki=ds[i]-row[10+i]
    if fy[v]==4 and row[10+i]>=8 and ki>6+iy[v]-jy[v]:okay=False;break
    if row[10+i]>=8 or ds[i]>=17 or (fy[v]==5 and ds[i]>=16):
     if not clean[v] or not len(links[v])<=ki<=len(links[v])+(esc[v] if ki<8 else 0):okay=False;break
   if not okay:continue
   if any(not off[V]<=row[c]<=off[V]+sum(bounds[j][1] for j in buckets[V]) for V,c in features):continue
   live.append(row)
  cols=list(range(len(bounds),len(bounds)+len(live)));bounds.extend([(0,1)]*len(cols));sizes.append(len(live));all_anchor_rows.append(tuple(live))
  put(f'anchor:{pos}-choice',dict.fromkeys(cols,1),1)
  for V,c in features:
   terms=dict.fromkeys(buckets[V],1);terms.update({j:-r[c] for j,r in zip(cols,live)})
   put(f'anchor:{pos}-trace:{sum(1<<v for v in V)}',terms,-off[V])
  DD=[degrees(r) for r in live]
  for i,v in enumerate(T,1):
   # Whole-component exterior singleton pool: isolation gives at least
   # 6/9/10 surviving triples from central singleton size8/9/10.
   # The six-point C5 split at degree16 and universal high-link split at
   # degree17 keep the whole far component outside this six-point support.
   lower={8:6,9:9,10:10}
   costs=[r[10+i] if ds[i]>=17 or (fy[v]==5 and ds[i]>=16)
          or (r[10+i]>=8 and ds[i]-r[10+i]>=8)
          else lower.get(r[10+i],0) for r,ds in zip(live,DD)]
   terms={U.index((v,)):-1};terms.update({j:c for j,c in zip(cols,costs) if c})
   ups.append((f'whole-pool:{pos}:{v}',terms,0))
   terms=dict(pool);terms.update({j:{9:5,10:7}[r[10+i]] for j,r in zip(cols,live) if r[10+i]>=9})
   ups.append((f'pool-conditional:{pos}:{v}',terms,27))
   for d,h in sels[v].items():
    terms={h:-1};terms.update({j:1 for j,ds in zip(cols,DD) if ds[i]==d})
    put(f'anchor:{pos}-degree:{v}:{d}',terms,0)
 return dict(case=case,bounds=bounds,upper=ups+pair_constraints(m)+[('H27-singleton-pool',{U.index((v,)):1 for v in range(6)},27)],equal=eq,quads=U,zero=zero,objective=[0]*len(bounds),target=0,live_sizes=sizes,internal_degrees=iy,internal_cover_degrees=jy,caps=caps,anchor_rows=all_anchor_rows,degree_selectors=sels)


def pair_constraints(comp):
 ups=[];M=models(comp)
 for y in range(6):
  st=[set(T)-{y} for T in M if y in T]
  cov=[set(p) for p in combinations([v for v in range(6) if v!=y],2) if all(set(p)&E for E in st)]
  exclusions=[None] if not cov else sorted(cov[0])
  for ex in exclusions:
   ids=[j for j,T in enumerate(U) if len(T)==2 and y in T and (ex is None or ex not in T)]
   h=U.index((y,))
   ups.extend([(f'pair:{y}:{ex}',dict.fromkeys(ids,1),6),(f'pair-singleton:{y}:{ex}',{h:5,**dict.fromkeys(ids,9)},59)])
 return ups

def matrix(rows,n):
 import numpy as np
 from scipy.sparse import coo_matrix
 ii=[];jj=[];vv=[]
 for i,(_,terms,_) in enumerate(rows):
  for j,v in terms.items():ii.append(i);jj.append(j);vv.append(v)
 return coo_matrix((np.asarray(vv,dtype=float),(ii,jj)),shape=(len(rows),n)).tocsr(),np.array([rhs for _,_,rhs in rows],dtype=float)

def run(component,case_index,seconds=25):
 import numpy as np
 from scipy.sparse import hstack,vstack
 from scipy.optimize import linprog
 start=time.monotonic();rec=catalog(component)['records'][case_index]
 case=dict(id=rec['id'],component=component,outside=ROOT_DEGREE-component,r10=0,r9=0,interiors=rec['interiors'])
 data=build(case);n=len(data['bounds']);A,b=matrix(data['upper'],n);E,f=matrix(data['equal'],n)
 AA=vstack((A,E,-E)).tocsr();bb=np.r_[b,f,-f]
 AA=hstack((AA,-np.ones((len(bb),1)))).tocsr();c=np.zeros(n+1);c[-1]=1
 sol=linprog(c,A_ub=AA,b_ub=bb,bounds=data['bounds']+[(0,None)],method='highs',options={'time_limit':seconds})
 result=dict(case=case,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),local43_sha256=hashlib.sha256((SOURCE/'MU42/scripts/local43.py').read_bytes()).hexdigest(),status=int(sol.status),columns=n,upper_rows=len(b),equal_rows=len(f),live_sizes=data['live_sizes'],seconds=time.monotonic()-start,root_degree=ROOT_DEGREE,point_cap=POINT_CAP,mu=MU,min_used_degree=MIN_USED_DEGREE,adaptation_source=ADAPTATION_SOURCE,source_commit=SOURCE_COMMIT,pinned_dependencies=PINNED_DEPENDENCIES,ordinary_bridge_sha256={name:hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in ('D17-research.md','D18-R99-bridge.md','D19-singleton-I04.md','C5-internal-compatibility.md')},assurance='discovery plus exact integer box diagnostic; imported mu41 crowding/minimum7/cross15 and universal geometry; not Lean or branch closure')
 if sol.status==0:
  result['phaseone_slack']=float(sol.fun);scale=10**10;ws=[max(0,round(-v*scale)) for v in sol.ineqlin.marginals];q=[0]*n
  orig=vstack((A,E,-E)).tocsr()
  for i,w in enumerate(ws):
   if not w:continue
   for j in range(orig.indptr[i],orig.indptr[i+1]):q[int(orig.indices[j])]+=w*int(orig.data[j])
  H=sum(w*int(v) for w,v in zip(ws,bb));minimum=sum(min(int(l)*v,int(u)*v) for (l,u),v in zip(data['bounds'],q))
  result['certificate']={'scale':scale,'H':H,'minimum':minimum,'G':H-minimum,'negative':H<minimum,'weights':[[i,w] for i,w in enumerate(ws) if w]}
  if not H<minimum:
   result['trace_solution']=[[list(U[j]),float(sol.x[j])] for j in range(41) if sol.x[j]>1e-7]
 out=Path(__file__).resolve().parent/'degree17';out.mkdir(exist_ok=True);(out/(case['id']+'.json')).write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k not in ('certificate','trace_solution')},separators=(',',':')),flush=True)
 if 'certificate'in result:print('exact gap',result['certificate']['G'],'negative',result['certificate']['negative'],flush=True)
 return result
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--component',type=int,choices=(9,10),default=10);ap.add_argument('--index',type=int,default=0);ap.add_argument('--seconds',type=int,default=25);a=ap.parse_args();run(a.component,a.index,a.seconds)
