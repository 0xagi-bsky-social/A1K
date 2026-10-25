import sys,itertools,json,time
sys.path.insert(0,'work/frontier20261019/search/vendor')
import z3
TEN=((0,1,2),(0,1,3),(0,2,4),(0,3,5),(0,4,5),(1,2,5),(1,3,4),(1,4,5),(2,3,4),(2,3,5))
def m(xs):return sum(1<<x for x in xs)
L=list(map(m,TEN))+[m(i+6 for i in t) for t in TEN]
def sf(a,b,c):return a&b==a&c==b&c
for P in [m((0,1)),m((0,6))]:
 C=[m(t) for t in itertools.combinations(range(12),4) if not m(t)&P and all(m(t)&s or P&s for s in L)]
 X=[z3.Bool('x'+str(i)) for i in range(len(C))];S=z3.Solver()
 forb=[(i,j) for i,j in itertools.combinations(range(len(C)),2) if not C[i]&C[j] or any(sf(C[i],C[j],h) for h in L)]
 S.add([z3.Or(z3.Not(X[i]),z3.Not(X[j])) for i,j in forb])
 bad=[(i,j,k) for i,j,k in itertools.combinations(range(len(C)),3) if sf(C[i],C[j],C[k])]
 S.add([z3.Or(z3.Not(X[i]),z3.Not(X[j]),z3.Not(X[k])) for i,j,k in bad])
 for q in range(len(C),0,-1):
  S.push();S.add(z3.PbGe([(x,1) for x in X],q));r=S.check()
  if r==z3.sat:
   mo=S.model();sel=[C[i] for i,x in enumerate(X) if z3.is_true(mo.eval(x))]
   print(json.dumps(dict(P=P,candidates=len(C),pair_conflicts=len(forb),triple_conflicts=len(bad),maximum=q,witness=sel)),flush=True);break
  S.pop()
