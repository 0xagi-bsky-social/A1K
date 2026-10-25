from itertools import combinations,product
import json
D=[frozenset(x) for x in [(0,1,2),(0,1,3),(0,2,4),(0,3,5),(0,4,5),(1,2,5),(1,3,4),(1,4,5),(2,3,4),(2,3,5)]]
D2=[frozenset(x+6 for x in T) for T in D]
stars=[T|{12} for T in D+D2]
def sf(A,B,C):return len({A,B,C})==3 and A&B==A&C==B&C
counts={'empty_coordinate_pair':0,'equal_coordinate_pair':0,'singleton_coordinate_pair':0}
violations=[]
for a,b in product(range(6),range(6,12)):
 R=frozenset([a,b,13,14]);pa=[T-{a} for T in D if a in T];pb=[T-{b} for T in D2 if b in T]
 comp=[(P,Q,P|Q) for P,Q in product(pa,pb)]
 for (P,Q,S),(P2,Q2,S2) in combinations(comp,2):
  if Q&Q2 and P&P2:continue
  if not Q&Q2:
   k=len(P&P2)
  else:k=len(Q&Q2)
  counts[{0:'empty_coordinate_pair',1:'singleton_coordinate_pair',2:'equal_coordinate_pair'}[k]]+=1
  if not any(sf(S,S2,T) for T in stars+[R]):violations.append([a,b,sorted(S),sorted(S2)])
def compositions(total,n,prefix=()):
 if n==1:
  yield prefix+(total,);return
 for v in range(total+1):yield from compositions(total-v,n-1,prefix+(v,))
pairs=[frozenset(P) for P in combinations(range(6),2)]
exts={P:frozenset(next(iter(T-P)) for T in D if P<T) for P in pairs}
wc=0;heavy_max=0;bad_weights=[]
for total in range(11):
 for w in compositions(total,6):
  wc+=1
  heavy=[P for P in pairs if sum(w[a] for a in exts[P])>=9]
  heavy_max=max(heavy_max,len(heavy))
  if heavy and (not set.intersection(*(set(exts[P]) for P in heavy)) or len(heavy)>5):bad_weights.append(w)
out={'split_completion_pairs_tested':10800,'incompatible_coordinate_cases':counts,'missing_sunflower_witnesses':violations,'nonnegative_integer_weights_sum_at_most_ten':wc,'max_heavy_keys':heavy_max,'heavy_key_counterexamples':bad_weights,'scope':'Explicit inherited six-point design; finite diagnostic supplements direct abstract proof, not a replacement for isomorphism or Lean proof.'}
print(json.dumps(out,indent=2))
