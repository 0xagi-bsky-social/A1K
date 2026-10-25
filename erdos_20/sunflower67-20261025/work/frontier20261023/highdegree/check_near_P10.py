#!/usr/bin/env python3
"""Small exhaustive corroboration of NP10's trace-witness lemma, no LP.
The ordinary arbitrary-support proof is in D18-pool-research.md.
"""
from itertools import combinations
from pathlib import Path
import hashlib,json,time
P=[sum(1<<int(v) for v in t) for t in '012 015 023 034 045 124 134 135 235 245'.split()]
S=[sum(1<<v for v in t) for k in range(1,5) for t in combinations(range(6),k)]
witness={s:[(1<<i)|(1<<(10+j)) for i,a in enumerate(P) for j,b in enumerate(P) if a&b==a&s==b&s] for s in S}
def valid(omitted):
 for s in S:
  exceptional=s in P and bool(omitted&((1<<P.index(s))|(1<<(10+P.index(s)))))
  if not exceptional and not any(not omitted&w for w in witness[s]):return s
 return None
start=time.monotonic();count=0
for k in range(4):
 for inds in combinations(range(20),k):
  omitted=sum(1<<i for i in inds);assert valid(omitted) is None;count+=1
control=None
for inds in combinations(range(20),4):
 omitted=sum(1<<i for i in inds);bad=valid(omitted)
 if bad is not None:control={'omitted_membership_indices':list(inds),'uncovered_trace':[v for v in range(6) if bad>>v&1]};break
assert control is not None,'Expected threshold-extension negative control to fail'
r={'result':'PASS','scope':'all literal trace witnesses for total membership omissions<=3; ordinary bridge separate; no Lean','tested_omission_patterns':count,'traces_per_pattern':len(S),'m4_false_extension_rejected':control,'seconds':time.monotonic()-start,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
p=Path(__file__).resolve().parent/'near-P10-check.json';p.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
