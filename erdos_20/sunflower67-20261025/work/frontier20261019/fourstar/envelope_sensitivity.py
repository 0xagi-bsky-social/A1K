from itertools import combinations_with_replacement
from pathlib import Path
import json
rows=[]
for budget in [58,59]:
 for drop in [None,'two_star','three_star','four_star']:
  vals=[]
  for d,c,b,a in combinations_with_replacement(range(1,20),4):
   if drop!='two_star' and a+b>34:continue
   if drop!='three_star' and a+b+c>46:continue
   if drop!='four_star' and a+b+c+d>60:continue
   L=max(0,a+b+c+d-28)
   U=budget*d+(a-d)*(a-1)+(b-d)*(b-1)+(c-d)*(c-1)
   vals.append((6*U-L*L+6*L,(a,b,c,d),L,U))
  v=max(x[0] for x in vals)
  rows.append({'excess_budget':budget,'dropped_constraint':drop,'admissible_count':len(vals),'maximum':v,'maximizers':[{'degrees':t,'L':L,'U':U} for score,t,L,U in vals if score==v],'required_lower_bound':4488,'diagnostic_contradiction':v<4488})
result={'assurance':'certificate-diagnostic; exact Python enumeration, no new Lean claim','scope':'Sensitivity of the necessary numerical relaxation only; maximizing degree tuples do not construct set families.','rows':rows}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
