from itertools import combinations
from pathlib import Path
import json
D={frozenset(t) for t in [(0,1,2),(1,2,3),(0,2,4),(0,1,5),(0,3,4),(0,3,5),(1,4,3),(1,4,5),(2,5,3),(2,5,4)]}
B={frozenset(v+6 for v in t) for t in D}; U=frozenset(range(6));V=frozenset(range(6,12))
hit3={frozenset(t) for t in combinations(range(6),3) if all(set(t)&s for s in D)}
assert hit3==D
hit6=[frozenset(t) for t in combinations(range(14),6) if all(set(t)&s for s in D|B)]
assert len(hit6)==100
assert all(t&U in D and t&V in B and t<=(U|V) for t in hit6)
assert all((U-t) not in D for t in D)
out={'three_subset_candidates':20,'three_transversals':len(hit3),'six_subset_candidates_including_two_extra_points':3003,'six_transversals':len(hit6),'foreign_point_transversals':sum(bool(t-{*U,*V}) for t in hit6),'scope':'Canonical finite check of minimum-transversal mechanism; generic proof additionally inspected'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
