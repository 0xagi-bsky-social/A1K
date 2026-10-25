import hashlib,importlib.util,itertools,json,sys,time
from pathlib import Path
root=Path('/home/user/Documents/Codex/2026-10-09/https-github-com-openai-math-blob/work/frontier20261023')
hd=root/'highdegree'
started=time.monotonic()
out={}
profiles=[]
for k in range(3,7):
 n=3*k-1
 total=24-4*k
 # Enumerate compositions directly; normalize with rotations of the reversed
 # tuple rather than the C++ indexing formula.
 def compositions(left,size):
  if size==0:
   if left==0: yield ()
   return
  for val in range(max(0,left-3*(size-1)),min(3,left)+1):
   for rest in compositions(left-val,size-1): yield (val,)+rest
 raw=0; reps=set()
 for r in compositions(total,n):
  raw+=1
  rev=r[::-1]
  reps.add(min(seq[shift:]+seq[:shift] for seq in (r,rev) for shift in range(n)))
 receipt=json.loads((hd/f'D16-fibre-k{k}-independent.json').read_text())
 actual=[tuple(x['r']) for x in receipt['reconstruction']['profiles']]
 profiles.append({'k':k,'raw_compositions':raw,'independent_representatives':len(reps),'receipt_rows':len(actual),'set_equal':reps==set(actual),'ordered_equal':sorted(reps)==actual,'missing':len(reps-set(actual)),'extra':len(set(actual)-reps),'complete':receipt['complete_conditional_k_exclusion']})
out['profile_domain']=profiles
# Alpha's counterexample motivates checking actual member labels, with repeated
# weights represented by distinct labels in each occupied fibre.
n=8; adjacent=[{j for j in range(n) if (j-i)%n in (3,4,5)} for i in range(n)]
comparisons=mismatches=cardinality_false_positive=0
witness=None
for t in itertools.product(range(3),repeat=n):
 d=[{(j,h) for j in adjacent[i] for h in range(t[j])} for i in range(n)]
 masks=[sum(1<<j for j in adjacent[i] if t[j]) for i in range(n)]
 for i in range(n):
  for j in range(n):
   actual=d[j]<=d[i]; mask=(masks[j]&~masks[i])==0
   comparisons+=1; mismatches+=actual!=mask
   if len(d[j])<=len(d[i]) and not actual:
    cardinality_false_positive+=1
    if witness is None: witness={'t':t,'i':i,'j':j,'q_i':len(d[i]),'q_j':len(d[j])}
out['weighted_inclusion']={'weight_vectors':3**n,'ordered_comparisons':comparisons,'mask_mismatches':mismatches,'cardinality_false_positives':cardinality_false_positive,'first_witness':witness}
# Importing this module does not load NumPy or a model; exercise only json_int.
spec=importlib.util.spec_from_file_location('checked_d19',hd/'replay_degree19.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
types=[]
for value in [True,False,1.0,49.0,'49',None,49,2**100]:
 try: res=m.json_int(value,'test'); status='accepted'
 except m.ReplayError: status='rejected'
 types.append({'value':value,'status':status})
out['integer_type_controls']=types
out['scientific_model_loaded']=any(name in sys.modules for name in ('numpy','scipy','degree19_replay_model'))
out['seconds']=time.monotonic()-started
Path('/tmp/r67_data_round07/checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
