import ast,gzip,hashlib,itertools,json
from collections import Counter
from pathlib import Path
root=Path('/home/user/Documents/Codex/2026-10-09/https-github-com-openai-math-blob/work/frontier20261023')
hd=root/'highdegree';out={}
def flower(a,b,c): return a&b==a&c==b&c
p10=[frozenset(map(int,s)) for s in '012 015 023 034 045 124 134 135 235 245'.split()]
link=p10+[frozenset(v+6 for v in t) for t in p10 if t!=frozenset((0,1,2))]
cones=[t|{99} for t in link]
# Extend Beta's proper-triple control to a repeated proper-pair trace.
controls=[]
for tail in [({0,6,7,100},{0,6,7,101}),({0,6,100,101},{0,6,100,102},{0,6,101,102})]:
 fam=cones+list(map(frozenset,tail));triples=list(itertools.combinations(fam,3))
 traces=Counter(tuple(sorted(q&set(range(12)))) for q in fam if 99 not in q)
 controls.append({'members':len(fam),'root_degree':sum(99 in q for q in fam),'member_triples_checked':len(triples),'sunflowers':sum(flower(*t) for t in triples),'proper_trace_counts':[(list(k),v) for k,v in traces.items()]})
out['multiplicity_controls']=controls
source=(hd/'degree19_projection_v5.py').read_text();tree=ast.parse(source)
upper=next(n for n in ast.walk(tree) if isinstance(n,ast.Dict) and all(isinstance(k,ast.Constant) for k in n.keys) and [k.value for k in n.keys]==[0,1,2,3,4])
out['source_upper_boxes']=ast.literal_eval(upper)
# Evaluate the exact frozen AST expression at the stage-forbidden interface.
source=(hd/'check_d17_stage_plan_v9.py').read_text();tree=ast.parse(source)
req=next(n for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='require' and len(n.args)>1 and isinstance(n.args[1],ast.JoinedStr) and 'unproved forbidden trace' in ast.unparse(n.args[1]))
predicate=compile(ast.Expression(req.args[0]),'<frozen stage predicate>','eval')
C=set(range(13));four={frozenset(t) for t in itertools.combinations(C,4)};three={frozenset(t) for t in itertools.combinations(C,3) if set(t)&set(range(6)) and set(t)&set(range(6,13))}
mask=lambda s:sum(1<<v for v in s)
trace_domain=[frozenset(t) for k in range(5) for t in itertools.combinations(range(14),k)]
results=[]
for name,F,T in [('empty',set(),set()),('full-four-only',four,set()),('proper-three-only',set(),three),('both',four,three)]:
 mismatches=accepted=0
 for S in trace_domain:
  Q=S|set(range(14,18-len(S)))
  direct=Q in F or frozenset(Q&C) in T
  actual=eval(predicate,{'c':mask(S&C),'prior_four':set(map(mask,F)),'prior_three':set(map(mask,T))})
  accepted+=bool(actual);mismatches+=bool(actual)!=direct
 results.append({'facts':name,'tests':len(trace_domain),'accepted':accepted,'mismatches':mismatches})
out['typed_absence_controls']={'source_sha256':hashlib.sha256(source.encode()).hexdigest(),'four_facts':len(four),'proper_three_facts':len(three),'results':results}
# Structural census independent of the tree replay's semantic pruning tests.
p=hd/'R15-rho6-cycle5-search.json.gz';raw=p.read_bytes();t=json.loads(gzip.decompress(raw));nodes=t['nodes']
child_counts=Counter(child for n in nodes for child in n.get('children',[]));ends=Counter(n.get('end','branch') for n in nodes)
reachable=set();stack=[0]
while stack:
 v=stack.pop()
 if v in reachable:continue
 reachable.add(v);stack.extend(nodes[v].get('children',[]))
receipt=json.loads((root/'review67/checks/round07/alpha/cycle5-replay.json').read_text())
out['tree_census']={'nodes':len(nodes),'branches':ends['branch'],'terminal_leaves':len(nodes)-ends['branch'],'histogram':dict(ends),'edges':sum(child_counts.values()),'nonroot_one_parent':all(child_counts[i]==1 for i in range(1,len(nodes))),'root_has_no_parent':child_counts[0]==0,'reachable':len(reachable),'fresh_replay_binds_tree':receipt['tree_sha256']==hashlib.sha256(raw).hexdigest(),'fresh_replay_counters_match':all(receipt['counts'][k]==ends[k] for k in ('count','min','colour','branch')),'supplied_controls_rejected':[n['name'] for n in receipt['negative_controls'] if n['rejected']]}
Path('/tmp/r67_data_round08/checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
