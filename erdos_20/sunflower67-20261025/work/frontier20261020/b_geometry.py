"""Exact diagnostic: exhaustive two-star geometries, no Lean assurance."""
import itertools as it
import json, pathlib, time

OUT = pathlib.Path(__file__).resolve().parent
TEN = ((0,1,2),(0,1,3),(0,2,4),(0,3,5),(0,4,5),
       (1,2,5),(1,3,4),(1,4,5),(2,3,4),(2,3,5))
def mask(xs): return sum(1 << x for x in xs)
CAN = tuple(sorted(map(mask,TEN)))
def permute(s,p): return mask(p[i] for i in range(len(p)) if s>>i&1)
perms=list(it.permutations(range(6)))
autos=[p for p in perms if tuple(sorted(permute(s,p) for s in CAN))==CAN]
designs=sorted({tuple(sorted(permute(s,p) for s in CAN)) for p in perms})
assert len(autos)==60 and len(designs)==12

# Three-colourings of a six-point design. 0 means absent from second support,
# 1 its first component, 2 its second component. Preserve all orbits.
unseen=set(it.product(range(3),repeat=6)); reps=[]
while unseen:
    c=min(unseen); orbit={tuple(c[p[i]] for i in range(6)) for p in autos}
    unseen-=orbit; reps.append(c)
partitions=set()
for a,b in it.product(reps,repeat=2):
    for n0 in range(4):
        for n1 in range(4-n0):
            n2=3-n0-n1
            c=a+b+(0,)*n0+(1,)*n1+(2,)*n2
            if c.count(1)==6 and c.count(2)==6:
                A=mask(i for i,v in enumerate(c) if v==1)
                B=mask(i for i,v in enumerate(c) if v==2)
                partitions.add(tuple(sorted((A,B))))
data={"assurance":"certificate-diagnostic", "automorphisms":autos,
      "designs":designs,"color_orbits":len(reps),
      "support_partition_representatives":sorted(partitions)}
(OUT/"b_geometry_data.json").write_text(json.dumps(data))
(OUT/"b_geometry_data.txt").write_text(
    f"{len(partitions)}\n" +
    "\n".join(f"{a} {b}" for a,b in sorted(partitions)) + "\n" +
    "\n".join(" ".join(map(str,d)) for d in designs) + "\n")
print(json.dumps({"automorphisms":len(autos),"designs":len(designs),
                  "color_orbits":len(reps),"partitions":len(partitions),
                  "cases_before_extra_symmetry":144*len(partitions)}))
