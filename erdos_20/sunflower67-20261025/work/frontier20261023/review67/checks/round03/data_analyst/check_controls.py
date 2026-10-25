import copy,hashlib,importlib.util,json,pathlib,signal,sys,time
sys.dont_write_bytecode=True
b=pathlib.Path('/home/user/Documents/Codex/2026-10-09/https-github-com-openai-math-blob/work/frontier20261023/highdegree')
p=b/'degree17_full/P9-Q8-complete-plan-v9.json'; original=json.loads(p.read_text()); original_hash=hashlib.sha256(p.read_bytes()).hexdigest()
spec=importlib.util.spec_from_file_location('stage',b/'check_d17_stage_plan_v9.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
out=pathlib.Path('/tmp/r67_data_round03'); rows=[]
signal.signal(signal.SIGALRM,lambda a,b:(_ for _ in ()).throw(TimeoutError('30s cap')))
def run(name,plan,partial=False):
 dest=out/(name+'.json');dest.write_text(json.dumps(plan));signal.alarm(30);start=time.monotonic()
 try:
  r=m.check(dest,partial);row=dict(name=name,accepted=True,status=r['status'],leaves=r['exact_leaf_count'],missing_four=len(r['missing_core_four']),missing_three=len(r['missing_mixed_core_three']),terminal=r['terminal']['applicable'])
 except Exception as e:row=dict(name=name,accepted=False,error=type(e).__name__+': '+str(e))
 finally:signal.alarm(0)
 row['seconds']=time.monotonic()-start;rows.append(row)
run('baseline',copy.deepcopy(original))
a=copy.deepcopy(original);a['nodes'].pop();run('omitted_final_mixed_three',a);run('omitted_final_mixed_three_partial',a,True)
a=copy.deepcopy(original);next(x for x in a['nodes'] if x['id']=='four-E4_56')['uses'].append('four-E4_57');run('forward_sibling',a)
a=copy.deepcopy(original);a['nodes'][0]['uses'].append(a['nodes'][0]['id']);run('self_dependency',a)
for name in ['target_equality','zero_scale','proper_trace_from_four_absence']:
 a=copy.deepcopy(original);node=next(x for x in a['nodes'] if x['id']==('four-E4_56' if name=='proper_trace_from_four_absence' else 'three-E3_00'))
 d=json.loads(pathlib.Path(node['receipt']).read_text())
 if name=='target_equality':
  d['dual']['upper_numerator']=51*d['dual']['scale'];d['dual']['H']=d['dual']['upper_numerator']-d['dual']['correction'];d['dual']['below51']=True
 elif name=='zero_scale':d['dual']['scale']=0
 else:d['forbidden'].append(67)
 dest=out/(name+'-receipt.json');dest.write_text(json.dumps(d));node['receipt']=str(dest);node['receipt_sha256']=hashlib.sha256(dest.read_bytes()).hexdigest();run(name,a)
result=dict(source_plan=str(p),source_plan_unchanged=hashlib.sha256(p.read_bytes()).hexdigest()==original_hash,checker_sha256=hashlib.sha256((b/'check_d17_stage_plan_v9.py').read_bytes()).hexdigest(),cases=rows,scope='Fresh bounded coverage/adversarial checks only; no model build, coefficient replay, solver or producer import')
(out/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
