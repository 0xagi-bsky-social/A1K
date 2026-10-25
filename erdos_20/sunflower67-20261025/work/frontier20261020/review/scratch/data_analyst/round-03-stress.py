import itertools,json
from fractions import Fraction
from pathlib import Path

def weights(n,total):
 if n==0:
  yield ()
 else:
  for w in range(total+1):
   for tail in weights(n-1,total-w):yield (w,)+tail

def common(pairs):
 x=set(pairs[0])
 for p in pairs[1:]: x.intersection_update(p)
 return x
ws=list(weights(6,10));pairs=list(itertools.combinations(range(6),2))
checks={}
for threshold in [9,7,6]:
 bad=[];nonempty=0
 for w in ws:
  heavy=[p for p in pairs if sum(w[i] for i in p)>=threshold]
  if not heavy:continue
  nonempty+=1
  if not common(heavy):bad.append({'weights':w,'heavy_pairs':heavy})
 checks[str(threshold)]={'vectors':len(ws),'nonempty_heavy_families':nonempty,'counterexamples':len(bad),'first_counterexample':bad[0] if bad else None}
incidence=[{'q':q,'cap':min((9*q)//2,(168-5*q)//3)} for q in range(13)]
trace_cases=[]
for pat in itertools.product(range(4),repeat=4):
 u=sum(bool(x&1) for x in pat);v=sum(bool(x&2) for x in pat);c=pat.count(3)
 if u>=3 and v>=3:trace_cases.append(c)
cycle=[{i,(i+1)%5} for i in range(5)]
cycle_intersecting=[mask.bit_count() for mask in range(32) if all(cycle[i]&cycle[j] for i in range(5) for j in range(i) if mask>>i&1 and mask>>j&1)]
edges=list(itertools.combinations(range(4),2))
graphs=[]
for mask in range(64):
 chosen=[e for i,e in enumerate(edges) if mask>>i&1]
 if max(sum(v in e for e in chosen) for v in range(4))<=2:graphs.append(len(chosen))
result={'weighted_pairs':checks,'incidence_caps':incidence,'maximum_integer_incidence_m':max(x['cap'] for x in incidence),'m41_q_lower':(82+8)//9,'m41_q_upper':(168-3*41)//5,'lp_intersection':{'m':str(Fraction(1512,37)),'q':str(Fraction(336,37))},'four_point_membership_assignments':4**4,'valid_three_trace_assignments':len(trace_cases),'minimum_common_trace':min(trace_cases),'C5_intersecting_edges_max':max(cycle_intersecting),'four_point_degree_two_graph_max_edges':max(graphs)}
print(json.dumps(result,indent=2))
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
