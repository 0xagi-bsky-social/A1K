"""Independent reparameterization: possible second design components for a low row."""
import itertools as it, json, pathlib
P=pathlib.Path(__file__).resolve().parent
D=json.loads((P/"b_geometry_data.json").read_text())
def mask(xs):return sum(1<<i for i in xs)
def lift(s,A):return mask(A[i] for i in range(6) if s>>i&1)
def permute(s,p):return mask(p[i] for i in range(6) if s>>i&1)
CAN=(7,11,21,26,28,38,41,44,49,50)
T=CAN+tuple(t<<6 for t in CAN)
triples=list(map(mask,it.combinations(range(15),3)))
index={s:i for i,s in enumerate(triples)}
comps=[]
for A in it.combinations(range(15),6):
    for d in D["designs"]:
        F=tuple(lift(t,A) for t in d)
        comps.append((mask(A),sum(1<<index[t] for t in F),F))
reps={}
for k in range(5):
    unseen=set(map(mask,it.combinations(range(6),k)));rr=[]
    while unseen:
        s=min(unseen);rr.append(s)
        unseen-={permute(s,p) for p in D["automorphisms"]}
    reps[k]=rr
rows=[]
for a in range(5):
    for b in range(a+1):
        c=4-a-b
        if not 0<=c<=3:continue
        for A,B in it.product(reps[a],reps[b]):
            R=A|(B<<6)|(((1<<c)-1)<<12)
            allowed=[s for s in triples if
                     all(not ((s&t)==(s&R)==(t&R)) for t in T)]
            bits=sum(1<<index[s] for s in allowed)
            good=[(S,F) for S,g,F in comps if g&~bits==0]
            pairs=[(S,V,F,G) for i,(S,F) in enumerate(good)
                   for V,G in good[:i] if not S&V]
            row={"trace_counts":[a,b,c],"row":R,
                 "allowed_triples":len(allowed),
                 "design_components":len(good),"disjoint_component_pairs":len(pairs),
                 "components":[{"support":S,"triples":F} for S,F in good],
                 "pairs":[[S,V] for S,V,F,G in pairs]}
            rows.append(row)
(P/"b_relative_row_result.json").write_text(json.dumps(rows,indent=2))
for r in rows:
    print({k:r[k] for k in r if k not in ("components","pairs")})
