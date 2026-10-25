"""Two pendant branch construction with exact block product verification."""
from reconstruct import *
from itertools import combinations,combinations_with_replacement,product
import json
# Glue F at original coordinates 2 and 3 to two separate copies of H at0.
attach=(2,3);remain=[i for i in range(10) if i not in attach]
def proj_f(s):return mask(j for j,i in enumerate(remain) if s>>i&1)
Hparts=[sorted({erase(h,0) for h in H if h&1==v}) for v in [0,1]]+[[0]]
# Return all realizable pairwise-difference masks for a sunflower triple.
ST={}
for a,b,c in product(range(3),repeat=3):
 ans={}
 for x,y,z in product(Hparts[a],Hparts[b],Hparts[c]):
  if x&y==x&z==y&z:
   d=(1 if x!=y else 0)|(2 if x!=z else 0)|(4 if y!=z else 0)
   ans.setdefault(d,[x,y,z])
 ST[a,b,c]=ans
SUB={}
for a,b in product(range(3),repeat=2):
 SUB[a,b]=next(((x,y) for x,y in product(Hparts[a],Hparts[b]) if x&y==x),None)
def rectangles(allcandidates=False):
 base=[(proj_f(f),1-((f>>2)&1),1-((f>>3)&1),'base',f) for f in F]
 extra=[]
 for edge in attach:
  P=[erase(f,edge) for f in F]
  if allcandidates:C=[s for s in range(1<<9) if all(s&v!=s for v in P)]
  else:
   A=sorted(set(Bp)-set(B))
   # send canonical attached edge2=(0,3) to edge3=(0,4): vertex3<->4.
   if edge==2:C=A
   else:
    # Lift9mask by adding no bit2 then permute K5vertices3,4 and erase edge3.
    C=[]
    perm=[0,1,2,4,3]
    for s in A:
     lifted=(s&3)|((s>>2)<<3)
     mapped=mask(EDGES.index(tuple(sorted((perm[u],perm[v])))) for j,(u,v) in enumerate(EDGES) if lifted>>j&1)
     C.append(erase(mapped,edge))
  other=5-edge
  other_small=other-(other>edge)
  for a in C:
   lift=(a&((1<<edge)-1))|((a>>edge)<<(edge+1))
   core=proj_f(lift);hclass=1-((a>>other_small)&1)
   extra.append((core,2 if edge==2 else hclass,hclass if edge==2 else 2,'extra'+str(edge),a))
 return base,extra
def badpair(r,s):
 if r[0]&s[0]==r[0] and SUB[r[1],s[1]] is not None and SUB[r[2],s[2]] is not None:return True
 if s[0]&r[0]==s[0] and SUB[s[1],r[1]] is not None and SUB[s[2],r[2]] is not None:return True
 return False
def badtriple(r,s,t):
 a,b,c=r[0],s[0],t[0]
 if a&b!=a&c or a&b!=b&c:return False
 d=(a!=b)|((a!=c)<<1)|((b!=c)<<2)
 return any((d|x|y)==7 for x in ST[r[1],s[1],t[1]] for y in ST[r[2],s[2],t[2]])
def counts(R):
 N=[0]*4
 for r in R:N[2*(r[0]&1)+((r[0]>>1)&1)]+=len(Hparts[r[1]])*len(Hparts[r[2]])
 return N
def check(R):
 badp=[ij for ij in combinations(range(len(R)),2) if badpair(*(R[i] for i in ij))]
 badt=[ijk for ijk in combinations_with_replacement(range(len(R)),3) if badtriple(*(R[i] for i in ijk))]
 return badp,badt
if __name__=='__main__':
 base,extra=rectangles()
 print('Nbase',counts(base),'Nextra',counts(extra),'base',len(base),'extra',len(extra))
 bp,bt=check(base+extra)
 print('badpairs',len(bp),'badtriples',len(bt),'examples',bp[:3],bt[:3])
 (ROOT/'two_branch_probe.json').write_text(json.dumps({'base':base,'extra':extra,'counts_base':counts(base),'counts_extra':counts(extra),'badpairs':bp,'badtriples':bt},indent=2)+'\n')

