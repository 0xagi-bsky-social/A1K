#!/usr/bin/env python3
"""Independent literal orbit and stage-premise coverage for D18 R99."""
from itertools import combinations, permutations, product
from pathlib import Path
import hashlib,json,time
p=Path(__file__).resolve().parent/'degree18_r99'
mask=lambda vs:sum(1<<v for v in vs)
D={mask(map(int,t)) for t in '015 023 034 045 124 134 135 235 245'.split()}
def move(s,q):return mask(q[v] for v in range(len(q)) if s>>v&1)
def read(n):return json.loads((p/n).read_text())
start=time.monotonic()
aut=[q for q in permutations(range(6)) if {move(s,q) for s in D}==D]
group=[a+tuple(v+6 for v in b)+(12,) for a,b in product(aut,repeat=2)]
group += [tuple(v+6 for v in a)+b+(12,) for a,b in product(aut,repeat=2)]
assert len(aut)==6 and len(set(group))==72
catalog=read('external-orbits.json');markers=catalog['markers'];orbits=catalog['orbits']
for k,m in markers.items():
 if k.startswith('E'):assert {move(m,q) for q in group}==set(orbits[k])
allq={mask(t) for t in combinations(range(12),4)}
internal={s for s in allq if s&63==s or s&(63<<6)==s}
iorbits={k:{move(markers[k],q) for q in group} for k in ('I01','I02','I03','I04')}
assert set.union(*iorbits.values())==internal and sum(map(len,iorbits.values()))==30
first=iorbits['I01']|iorbits['I03']
assert first==set(read('internal-stage1-exclusions.json')['forbidden'])
for k in ('I02','I04'):
 assert set(read(k+'-pooled-stage1-none.json')['forbidden'])==first
four=catalog['fourcore_cases']
assert len(four)==22 and sum(len(orbits[k]) for k in four)==465
assert set().union(*(set(orbits[k]) for k in four))==allq-internal
plan=read('mixed-stage-plan.json');mixed=plan['cases']
assert len(mixed)==8 and set(plan['forbidden'])==allq
mtarget={mask(t)|(1<<12) for t in combinations(range(12),3) if set(t)&set(range(6)) and set(t)&set(range(6,12))}
assert set().union(*(set(orbits[k]) for k in mixed))==mtarget
assert sum(len(orbits[k]) for k in mixed)==len(mtarget)==180
for k in mixed:
 assert set(read(k+'-mixed-both.json')['forbidden'])==allq
receipts=['I01-none.json','I03-none.json','I02-pooled-stage1-none.json','I04-pooled-stage1-none.json']
receipts += [k+'-fourcore-both.json' for k in four]+[k+'-mixed-both.json' for k in mixed]
assert all(read(n)['dual']['below50'] for n in receipts)
result={'result':'PASS','scope':'literal symmetry and staged-assumption coverage only; exact arithmetic and ordinary model bridge separate','group_size':72,'internal_orbit_sizes':{k:len(v) for k,v in iorbits.items()},'mixed_four_core_orbits':22,'mixed_four_core_sets':465,'mixed_three_core_orbits':8,'mixed_three_core_traces':180,'active_receipts':receipts,'seconds':time.monotonic()-start,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(p/'coverage-check.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='active_receipts'}))
