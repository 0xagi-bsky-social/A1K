#!/usr/bin/env python3
"""Literal finite coverage check, separate from projection builders and LP.
No universal combinatorial premises or Lean proof are certified here.
"""
from itertools import combinations, permutations, product
from pathlib import Path
import hashlib, json, time

HERE=Path(__file__).resolve().parent
OUT=HERE/'degree19'
SOURCE=HERE.parents[1]/'frontier20261020/prior-art68/repository/companion/upstream'
mask=lambda vs:sum(1<<v for v in vs)
D={mask(map(int,t)) for t in '012 015 023 034 045 124 134 135 235 245'.split()}
R=D-{7}
def move(s,p):return mask(p[v] for v in range(len(p)) if s>>v&1)
def autos(f):return [p for p in permutations(range(6)) if {move(t,p) for t in f}==f]
def read(name):return json.loads((OUT/name).read_text())
def sf(a,b,c):return a&b==a&c==b&c
def main():
 start=time.monotonic();ay,az=autos(D),autos(R)
 assert (len(ay),len(az))==(60,6)
 cat=json.loads((SOURCE/'D19/data/ORBIT_CATALOGUE.json').read_text())
 markers={r['id']:mask(r['mark']) for r in cat['internals']+cat['external']}
 ps=[tuple(y)+tuple(z+6 for z in zz)+(12,) for y,zz in product(ay,az)]
 ext={r['id']:{move(markers[r['id']],p) for p in ps} for r in cat['external']}
 target={mask(t) for t in combinations(range(12),4) if not (set(t)<=set(range(6)) or set(t)<=set(range(6,12)))}
 target|={mask(t)|(1<<12) for t in combinations(range(12),3)}
 assert len(target)==685 and set.union(*ext.values())==target
 assert sum(map(len,ext.values()))==len(target)
 stages=read('external-stage-exclusions.json')
 closed={k for k in ext if read(k+'-external-both.json').get('dual',{}).get('below49')}
 assert closed==set(stages['excluded_cases']) and len(closed)==23
 forbidden=set()
 for k in closed:
  for s in ext[k]:
   forbidden.add(s)
   if s>>12:forbidden.add(s^ (1<<12))
 assert forbidden==set(stages['forbidden_traces_on13'])
 for k in ('E09','E11','E15'):
  assert set(read(k+'-staged-both.json')['forbidden'])==forbidden
 remaining=target-set.union(*(ext[k] for k in closed|{'E09','E11','E15'}))
 assert remaining==ext['E22']|ext['E26']
 assert all(s>>12 and (s&4095)&63==0 for s in remaining)
 # The four P9 internal orbits partition all fifteen four-subsets.
 internal={k:{move(markers[k]>>6,p)<<6 for p in az} for k in ('I01','I02','I03','I04')}
 assert {k:sorted(v) for k,v in internal.items()}==read('internal-orbits.json')
 assert set.union(*internal.values())=={mask(t) for t in combinations(range(6,12),4)}
 assert len(internal['I04'])==3
 assert len(set.intersection(*(set(v for v in range(12) if s>>v&1) for s in internal['I04'])))==3
 single=read('Zsingle-cover-refined-none.json')['assigned']['Z']
 two=read('Zpattern08-none.json')['assigned']['Z']
 assert {tuple(sorted(move(s>>6,p)<<6 for s in single)) for p in az}=={(s,) for s in internal['I04']}
 assert {tuple(sorted(move(s>>6,p)<<6 for s in two)) for p in az}==set(combinations(sorted(internal['I04']),2))
 # Reconstruct the complete P10 internal family by augmentation, without
 # importing the discovery catalogue or any numerical optimization code.
 quads=[mask(t) for t in combinations(range(6),4)]
 cones=[s|(1<<6) for s in D];valid=set()
 def augment(chosen,start):
  valid.add(tuple(chosen))
  fixed=cones+chosen
  for i in range(start,15):
   q=quads[i]
   if not any(sf(q,a,b) for a,b in combinations(fixed,2)):augment(chosen+[q],i+1)
 augment([],0)
 yp=read('Y-patterns.json');covered=set()
 assert len(valid)==yp['valid_assignments']==292 and len(yp['orbits'])==13
 for i,o in enumerate(yp['orbits']):
  orbit={tuple(sorted(move(s,p) for s in o['members'])) for p in ay}
  assert len(orbit)==o['size'] and not covered&orbit
  covered|=orbit
  if i:assert read(f'Ypattern{i:02}-Z.json')['assigned']['Y']==o['members']
 assert covered=={tuple(sorted(t)) for t in valid}
 result=dict(result='PASS',scope='literal orbit and staged-assumption coverage; no LP, universal premise proof, or Lean',automorphisms=[60,6],external_orbits=len(ext),external_markers=len(target),first_stage_cases=len(closed),forbidden_traces=len(forbidden),remaining_markers=sorted(remaining),P9_internal_orbits={k:len(v) for k,v in internal.items()},P10_internal_assignments=len(valid),P10_internal_orbits=13,seconds=time.monotonic()-start,checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),catalogue_sha256=hashlib.sha256((SOURCE/'D19/data/ORBIT_CATALOGUE.json').read_bytes()).hexdigest())
 (OUT/'coverage-check.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
