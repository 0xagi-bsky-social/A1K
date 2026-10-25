"""Separate universal geometry generator, using verified six-colouring orbits."""
import itertools as it,json,pathlib
P=pathlib.Path(__file__).resolve().parent
D=json.loads((P/"b_geometry_data.json").read_text())
def mask(xs):return sum(1<<i for i in xs)
unseen=set(it.product(range(3),repeat=6));reps=[]
while unseen:
    c=min(unseen);reps.append(c)
    unseen-={tuple(c[p[i]] for i in range(6)) for p in D["automorphisms"]}
partitions=set()
for a,b in it.product(reps,repeat=2):
    c=a+b
    n1=6-c.count(1);n2=6-c.count(2)
    if min(n1,n2)<0:continue
    c=c+(1,)*n1+(2,)*n2
    A=mask(i for i,v in enumerate(c) if v==1)
    B=mask(i for i,v in enumerate(c) if v==2)
    partitions.add(tuple(sorted((A,B))))
(P/"b_universal_data.txt").write_text(str(len(partitions))+"\n"+
    "\n".join(f"{a} {b}" for a,b in sorted(partitions))+"\n"+
    "\n".join(" ".join(map(str,d)) for d in D["designs"])+"\n")
print(len(partitions))
