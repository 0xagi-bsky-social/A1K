from reconstruct import *
from itertools import combinations
import random,json,math
import numpy as np
alpha=(1127+math.sqrt(925536))**(1/17)
# count order: weight if core bit is 0 = leaf contains root; if bit1 = leaf avoids root.
leaves=[
 {'name':'none','u':1,'v':1,'cost':0},
 {'name':'F','u':31,'v':44,'cost':8},
 {'name':'H','u':46,'v':75,'cost':9},
 {'name':'BpF','u':1749,'v':2615,'cost':17},
 {'name':'BpH','u':1636,'v':2728,'cost':17},
 {'name':'G','u':98308,'v':152351,'cost':26}]
records=[]
def core_counts(fam,n,ports,choice,exact=False):
 N=[0]*4 if len(ports)==2 else [0]*2
 free=[j for j in range(n) if j not in ports]
 if exact:
  weights=[(leaves[t]['v'],leaves[t]['u']) for t in choice]
 else:
  weights=[(leaves[t]['v']/alpha**leaves[t]['cost'],leaves[t]['u']/alpha**leaves[t]['cost']) for t in choice]
 for s in fam:
  w=1
  for j,(z,o) in zip(free,weights): w*=o if s>>j&1 else z
  cls=((s>>ports[0])&1)
  if len(ports)==2:cls=2*cls+((s>>ports[1])&1)
  N[cls]+=w
 return N
def value(N):
 a,b,c,d=N[2],N[3],N[0],N[1]
 return (a+d+math.sqrt((a-d)**2+4*b*c))/2
best=alpha
random.seed(23)
for core,fam,n,pairs in [('F',F,10,[(0,1),(0,7)]),('H',H,11,[(0,1)]),('Bp',Bp,19,[(0,1),(0,3),(0,9),(9,10)])]:
 for pp in pairs:
  free=[j for j in range(n) if j not in pp]
  for trial in range(15):
   choice=[random.randrange(len(leaves)) if trial else 0 for _ in free]
   bits=np.array([[(s>>j)&1 for s in fam] for j in free],dtype=bool)
   classes=np.array([2*((s>>pp[0])&1)+((s>>pp[1])&1) for s in fam])
   norm=[(l['v']/alpha**l['cost'],l['u']/alpha**l['cost']) for l in leaves]
   W=np.ones(len(fam))
   for bi,t in zip(bits,choice): W*=np.where(bi,norm[t][1],norm[t][0])
   score=value(np.bincount(classes,weights=W,minlength=4))
   for sweep in range(30):
    changed=False
    for i in random.sample(range(len(free)),len(free)):
     old=choice[i];bestt=old;bi=bits[i]
     W0=W/np.where(bi,norm[old][1],norm[old][0])
     N0=np.bincount(classes,weights=W0*(~bi),minlength=4)
     N1=np.bincount(classes,weights=W0*bi,minlength=4)
     for t,(v,u) in enumerate(norm):
      val=value(N0*v+N1*u)
      if val>score+1e-11:score=val;bestt=t
     choice[i]=bestt
     W=W0*np.where(bi,norm[bestt][1],norm[bestt][0])
     changed|=bestt!=old
    if not changed:break
   cost=n-2+sum(leaves[t]['cost'] for t in choice)
   exact=core_counts(fam,n,pp,choice,True)
   rate=value(exact)**(1/cost)
   if rate>best+1e-13:
    best=rate
    row={'core':core,'ports':pp,'attachments':[(j,leaves[t]['name']) for j,t in zip(free,choice) if t], 'exponent':cost,'N':exact,'rate_diagnostic':rate}
    print(row,flush=True);records.append(row)
    (ROOT/'tree_search.json').write_text(json.dumps(records,indent=2)+'\n')
 print('done',core,best,flush=True)
(ROOT/'tree_search.json').write_text(json.dumps(records,indent=2)+'\n')

