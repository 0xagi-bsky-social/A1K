from reconstruct import *
from itertools import product
import json,math
rows=json.loads((ROOT/'port_scan.json').read_text())
items=[]
seen=set()
for family in ['F','H','Bp']:
 for r in rows[family]:
  for T in [r['matrix'],[r['matrix'][3],r['matrix'][1],r['matrix'][2],r['matrix'][0]]]:
   key=(tuple(T),8 if family=='F' else 9 if family=='H' else 17)
   if key in seen: continue
   seen.add(key);items.append((family,r['ports'],T,key[1]))
def mul(A,B):
 a,b,c,d=A;e,f,g,h=B
 return (a*e+b*g,a*f+b*h,c*e+d*g,c*f+d*h)
def rate(A,w):
 a,b,c,d=A
 return math.exp(math.log((a+d+math.sqrt((a-d)**2+4*b*c))/2)/w)
best=(0,None)
records=[]
def go(A,w,word,k):
 global best
 if k:
  r=rate(A,w)
  if r>best[0]+1e-14:
   best=(r,word);records.append((r,word,A,w))
 if k==7:return
 for i,item in enumerate(items):
  if k==0 and i>0:continue
  go(mul(A,item[2]),w+item[3],word+[i],k+1)
# separately all length<=6 allowing any start
def go2(A,w,word,k):
 global best
 if k:
  r=rate(A,w)
  if r>best[0]+1e-14:
   best=(r,word);records.append((r,word,A,w));print(records[-1],flush=True)
 if k==6:return
 for i,item in enumerate(items):go2(mul(A,item[2]),w+item[3],word+[i],k+1)
go2((1,0,0,1),0,[],0)
(ROOT/'matrix_words.json').write_text(json.dumps({'items':items,'records':records},indent=2)+'\n')
print('best',best)

