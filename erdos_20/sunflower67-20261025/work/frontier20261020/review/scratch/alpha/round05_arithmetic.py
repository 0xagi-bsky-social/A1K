from itertools import combinations
from pathlib import Path
import json
# Finite exact arithmetic consequences of the two displayed incidence inequalities.
feasible=[(m,q) for m in range(100) for q in range(13) if 2*m<=9*q and 3*m<=168-5*q]
assert max(m for m,q in feasible)==40
at40=[q for m,q in feasible if m==40]
assert at40==[9]
assert 1512//37==40 and 1512<37*41
# Census before and after the completion bound; n2>=15 already ensures a row exists.
raw=[(a,b,c) for a in range(62) for b in range(62) for c in range(28) if a+b+c==61 and b+2*c==76]
assert min(c for a,b,c in raw)==15
refined=[t for t in raw if t[0]>=9]
assert refined==[(9,28,24),(10,26,25),(11,24,26),(12,22,27)]
assert (4*19+40-2)//2==57 and (2*19+2*14+40-2)//2==52
# Graph cap over the entire six-edge ground graph, including empty/small cases.
edges=list(combinations(range(4),2));allowed=[]
for bits in range(64):
 E=[e for i,e in enumerate(edges) if bits>>i&1]
 if all(sum(v in e for e in E)<=2 for v in range(4)):allowed.append(E)
assert max(map(len,allowed))==4
out={'incidence_max_m':40,'q_at_m40':at40,'floor_1512_over_37':1512//37,'census_before_nine_min_n2':min(t[2] for t in raw),'refined_census':refined,'general_closed_meeting_cap':57,'H2_closed_meeting_cap':52,'minimum_H2_disjoint_completions':61-52,'max_outsider_graph_edges':max(map(len,allowed)),'scope':'Exact checks of stated inequalities and four-vertex graphs only; no family existence or new global bound claim'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
