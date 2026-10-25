from itertools import combinations
import json

def scalar_max(cap_single, cap_overlap):
    candidates=[]
    for q in range(13):
        for m in range(62):
            if 2*m<=cap_overlap*q and 3*m<=cap_single*(12-q)+cap_overlap*q:
                candidates.append((m,q))
    best=max(m for m,q in candidates)
    return {'max_residual':best,'maximizers':[(m,q) for m,q in candidates if m==best]}

cycle=[frozenset([i,(i+1)%5]) for i in range(5)]
intersecting=[]
for k in range(6):
    for fam in combinations(cycle,k):
        if all(a & b for a,b in combinations(fam,2)):intersecting.append(fam)
cmax=max(map(len,intersecting))
graph_edges=list(map(frozenset,combinations(range(4),2)))
free=[]
for k in range(7):
    for fam in combinations(graph_edges,k):
        if not any(a&b==a&c==b&c for a,b,c in combinations(fam,3)):free.append(fam)
gmax=max(map(len,free))
result={'exact_caps_14_9':scalar_max(14,9),'relaxed_caps_15_10':scalar_max(15,10),'C5_intersecting_max':cmax,'C5_product_bound':cmax*cmax,'four_vertex_sunflower_free_edge_max':gmax,'four_vertex_maximizers':len([f for f in free if len(f)==gmax]),'qualification':'Finite checks of the scalar relaxation and small auxiliary graphs, not actual-family realizability or a new Lean theorem.'}
print(json.dumps(result,indent=2))
