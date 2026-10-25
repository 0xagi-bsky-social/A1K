"""Exploration only; exact seed reconstruction and finite elementary checks."""
from itertools import combinations
from pathlib import Path
import json, math

ROOT=Path(__file__).resolve().parent
def mask(it): return sum(1<<i for i in set(it))
EDGES=list(combinations(range(5),2))
def degseq(m):
 d=[0]*5
 for i,(u,v) in enumerate(EDGES):
  if m>>i&1: d[u]+=1; d[v]+=1
 return sorted(d)
F=[]
for m in range(1<<10):
 k=m.bit_count()
 if (k==4 and degseq(m)==[1,1,1,1,4]) or (k==6 and degseq(m)==[2,2,2,3,3] and any(all(bool(m>>(EDGES.index(tuple(sorted((u,v)))))&1)==((u in part)!=(v in part)) for u,v in EDGES) for part in combinations(range(5),2))) or (k==6 and degseq(1023^m)==[1,1,1,2,3]):
  F.append(m)
H=sorted({mask((a*x+b)%11 for x in S) for S in [{0,1,2,3,4,5,6},{0,1,2,3,4,6,7},{0,1,2,6,9}] for a in [1,3,4,5,9] for b in range(11)})
def erase(m,p): return (m&((1<<p)-1)) | ((m>>(p+1))<<p)
B=sorted({erase(f,2)|(erase(h,0)<<9) for f in F for h in H if ((f>>2)&1)!=(h&1)})
Bp=sorted(sum(1<<int(s) for s in l.split()) for l in (ROOT/'upstream/Bprime.txt').read_text().splitlines() if l.strip() and not l.startswith('#'))
def triple_check(A):
 return next(((a,b,c) for a,b,c in combinations(A,3) if a&b==a&c==b&c),None)
def sperner_check(A):
 return next(((a,b) for a,b in combinations(A,2) if a&b in (a,b)),None)
def ports(A,n):
 out=[]
 for p,q in combinations(range(n),2):
  c=[0]*4
  for s in A: c[((s>>p)&1)*2+((s>>q)&1)]+=1
  # [[N10,N11],[N00,N01]]
  T=[c[2],c[3],c[0],c[1]]
  a,b,c0,d=T
  rate=((a+d+math.sqrt((a-d)**2+4*b*c0))/2)**(1/(n-2))
  out.append(dict(ports=[p,q],matrix=T,exploratory_rate=rate))
 return sorted(out,key=lambda x:-x['exploratory_rate'])
def main():
 assert len(F)==75 and len(H)==121 and len(B)==4349 and len(Bp)==4364
 assert set(B)<=set(Bp)
 assert not triple_check(F) and not triple_check(H)
 assert not sperner_check(F) and not sperner_check(H)
 assert len(Bp)==len(set(Bp)) and not sperner_check(Bp)
 out={n:ports(A,m) for n,A,m in [('F',F,10),('H',H,11),('B',B,19),('Bp',Bp,19)]}
 (ROOT/'port_scan.json').write_text(json.dumps(out,indent=2)+'\n')
 (ROOT/'seeds.json').write_text(json.dumps({'F':F,'H':H,'B':B,'Bp':Bp,'extra':sorted(set(Bp)-set(B))},indent=2)+'\n')
 for n,v in out.items(): print(n, v[:4])
 print('extra',sorted(set(Bp)-set(B)))
if __name__=='__main__': main()

