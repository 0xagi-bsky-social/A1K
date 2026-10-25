import itertools as I,json,pathlib
P=pathlib.Path(__file__).resolve().parent
m=lambda xs:sum(1<<i for i in xs)
TEN=[m(x) for x in [(0,1,2),(0,1,3),(0,2,4),(0,3,5),(0,4,5),(1,2,5),(1,3,4),(1,4,5),(2,3,4),(2,3,5)]]
T=TEN+[t<<6 for t in TEN]
def per(t,p):return m(p[i] for i in range(6) if t>>i&1)
autos=[p for p in I.permutations(range(6)) if sorted(per(t,p) for t in TEN)==sorted(TEN)]
reps={k:sorted({min(per(t,p) for p in autos) for t in map(m,I.combinations(range(6),k))}) for k in range(5)}
rows=[]
for a in range(5):
 for b in range(a+1):
  c=4-a-b
  if c<0:continue
  for A,B in I.product(reps[a],reps[b]):
   R=A|(B<<6)|(((1<<c)-1)<<12);z=1<<16
   edges=[(i,j) for i,j in I.combinations(range(16),2) if all(not(t&(z|(1<<i)|(1<<j))==t&R==(z|(1<<i)|(1<<j))&R) for t in T)]
   adj={i:set() for i in range(16)}
   for i,j in edges:adj[i].add(j);adj[j].add(i)
   cycles=[]
   def walk(path):
    if len(path)==5:
     if path[0] in adj[path[-1]]:cycles.append(path)
     return
    for j in adj[path[-1]]:
     if j>path[0] and j not in path:walk(path+[j])
   for i in range(16):walk([i])
   # Directly check additionalfreshpoint17 produces noallowed pairs.
   extra=[j for j in range(16) if all(not(t&(z|(1<<17)|(1<<j))==t&R==(z|(1<<17)|(1<<j))&R) for t in T)]
   row={'trace':[a,b,c],'R':R,'allowed_pairs':edges,'five_cycles':cycles,'additional_fresh_allowed':extra}
   rows.append(row)
   print(row)
(P/'fresh_link_vertex.json').write_text(json.dumps({'assurance':'certificate-diagnostic','cases':rows},indent=2))
