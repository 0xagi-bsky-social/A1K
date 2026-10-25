import itertools as I,json,pathlib,time
P=pathlib.Path(__file__).resolve().parent
m=lambda xs:sum(1<<x for x in xs)
TEN=[m(x) for x in ((0,1,2),(0,1,3),(0,2,4),(0,3,5),(0,4,5),(1,2,5),(1,3,4),(1,4,5),(2,3,4),(2,3,5))]
L=TEN+[t<<6 for t in TEN]
sf=lambda a,b,c:a&b==a&c==b&c
rows=[]
for a in range(6):
 for b in range(6,12):
  p=(1<<a)|(1<<b)
  C=[m(t) for t in I.combinations(range(12),4) if not m(t)&p and all((m(t)|p)&s for s in L)]
  assert len(C)==25
  left=sorted({x&63 for x in C});right=sorted({x>>6 for x in C})
  assert len(left)==len(right)==5
  assert all(sum(bool(x&y) for y in left if x!=y)==2 for x in left)
  assert all(sum(bool(x&y) for y in right if x!=y)==2 for x in right)
  for x,y in I.combinations(C,2):
   compatible=bool(x&y) and not any(sf(x,y,t) for t in L)
   product_compatible=bool((x&63)&(y&63)) and bool((x>>6)&(y>>6))
   assert compatible==product_compatible
  # No three distinct pairwise-intersecting coordinate pairs; max coordinate clique2.
  assert not any(all(x&y for x,y in I.combinations(t,2)) for t in I.combinations(left,3))
  assert not any(all(x&y for x,y in I.combinations(t,2)) for t in I.combinations(right,3))
  rows.append({'a':a,'b':b,'completions':C,'left_cycle':left,'right_cycle':right,'max_compatible_bound':4})
# Extension pair map is a bijection, verified directly for each canonical pair.
ext={}
for p in map(m,I.combinations(range(6),2)):
 e=[t^p for t in TEN if t&p==p];assert len(e)==2
 ext[p]=e[0]|e[1]
assert len(set(ext.values()))==15
out={'assurance':'certificate-diagnostic','split_pairs_checked':36,'structural_model':'Cartesian product of two C5 edge-intersection graphs; each clique projects to size≤2, hence≤4','cases':rows,'extension_pair_bijection':ext}
(P/'verify_a_split.json').write_text(json.dumps(out,indent=2));print('PASS:36 split pairs; each25 graph equals C5 strong-product; clique≤4; extension pair map bijective')
