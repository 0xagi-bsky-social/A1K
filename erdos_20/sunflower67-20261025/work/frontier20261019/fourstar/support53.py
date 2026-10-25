from itertools import combinations_with_replacement
import json
rows=[]
for aa in combinations_with_replacement(range(1,20),4):
 a,b,c,d=aa[::-1]
 if a+b>34 or a+b+c>46 or a+b+c+d>60:continue
 L=max(0,a+b+c+d-28)
 U=58*d+(a-d)*(a-1)+(b-d)*(b-1)+(c-d)*(c-1)
 score=6*U-L*L+6*L
 rows.append(dict(a=a,b=b,c=c,d=d,L=L,U=U,score=score))
m=max(x['score'] for x in rows)
# Monotonicity in d lets the formal numerical leaf use only three finite variables.
reduced=[]
for a in range(20):
 for b in range(20):
  for c in range(20):
   if not (1<=c<=b<=a<=19 and a+b<=34 and a+b+c<=46):continue
   d=min(c,60-a-b-c)
   L=max(0,a+b+c+d-28)
   U=58*d+(a-d)*(a-1)+(b-d)*(b-1)+(c-d)*(c-1)
   reduced.append(6*U-L*L+6*L)
assert m==max(reduced)==4475
print(json.dumps({'scope':'exact finite arithmetic diagnostic, not universal family proof','admissible_quadruples':len(rows),'maximum':m,'maximizers':[x for x in rows if x['score']==m],'reduced_triple_count':len(reduced),'contradiction_threshold':4488,'margin':4488-m},indent=2))
