from pathlib import Path
import json,sys,hashlib,shutil
from datetime import datetime,timezone
sys.path.insert(0,'/home/user/.codex/skills/superresearch-x2/scripts')
from native_research import NativeRunStore,load_json,parse_json,seal_record,bytes_digest,validate_review_bundle
R=Path(__file__).resolve().parent
B=R.parent
def dump(p,v): p.write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n')
def now(): return datetime.now(timezone.utc).isoformat()
roles=['chief','domain_expert','literature_reviewer','methodologist','data_analyst','logic_auditor','citation_verifier','academic_writer','alpha','beta','copyeditor','typesetter']
expertise=['Extremal set theory and synthesis of proof assurance','Extremal hypergraphs, support bounds and triple design structure','Sunflower literature and primary-source prior art','Proof obligations, finite enumeration coverage and reproducibility','Exact integer combinatorics, grids and diagnostic computation','Quantifiers, double counting and Lean/prose semantics','Theorem locators, mathematical facts and source provenance','Rigorous mathematical exposition and contribution framing','Adversarial proof audit, counterexamples and overstatement','Constructive combinatorial repair and domain fit','Mathematical copyediting, attribution and bounded text reuse','Mathematical typography, artifact fidelity and visual QA']
cmd=sys.argv[1]
if cmd=='create':
 roster=[dict(agent_id='/root/review_coordinator/'+r,context_id='/root/review_coordinator/'+r,role=r,expertise=e,mandate='Perform distinct substantive '+r+' analysis for every synchronous review phase; preserve objections, evidence scope and isolation',provider='unknown',model='unknown') for r,e in zip(roles,expertise)]
 dump(R/'roster.json',roster)
 NativeRunStore.create(R/'run',load_json(R/'contract.json'),roster,limitations=['Actual separate collaboration contexts; same control environment and unknown provider/model metadata; no organizational independence','Local unsigned hashes and declared tool provenance only; no independent human certification','Bounded source and text comparison; no exhaustive originality claim'])
 print('created')
elif cmd=='open':
 n=int(sys.argv[2]);p=R/'public'/f'round-{n:02d}';p.mkdir(parents=True)
 shutil.copyfile(B/'manuscript'/'research-draft.md',p/'manuscript.md')
 state=load_json(R/'public-state.json') if (R/'public-state.json').exists() else {'coordinator_changes':['Made reflexive intersection convention explicit','Added literal checked universal three-star theorem and present receipt scope'],'review_status':'Round 1 begins; no specialist outputs yet'}
 ret=NativeRunStore(R/'run').open_round((p/'manuscript.md').read_bytes(),load_json(R/'evidence.json'),load_json(R/'verification.json'),state)
 dump(p/'snapshot.json',ret);shutil.copyfile(R/'contract.json',p/'contract.json');shutil.copyfile(R/'roster.json',p/'roster.json')
 print(json.dumps({'round':n,'snapshot_sha256':ret['snapshot_sha256'],'manuscript_sha256':ret['snapshot']['manuscript_sha256'],'directory':str(p)}))
elif cmd=='record':
 n=int(sys.argv[2]);role=sys.argv[3];p=R/'responses'/f'round-{n:02d}'/(role+'.json')
 response=p.read_text();body=parse_json(response);record=seal_record(body,{'tool':'collaboration.followup_task / specialist final response','call_id':f'local-log:frontier20261019-final/round-{n:02d}/{role}/actual-public-response','context_id':'/root/review_coordinator/'+role,'recorded_at':now(),'synthetic':False,'public_response':response,'response_sha256':bytes_digest(response.encode())})
 q=R/'sealed'/f'round-{n:02d}';q.mkdir(parents=True,exist_ok=True);dump(q/(role+'.json'),record)
 print(json.dumps(NativeRunStore(R/'run').record_submission(record)))
elif cmd=='commit':
 s=NativeRunStore(R/'run');row=s.commit_round();n=row['snapshot']['round'];p=R/'committed';p.mkdir(exist_ok=True);dump(p/f'round-{n:02d}.json',row)
 summary=[]
 for x in row['submissions']:
  c=x['content'];summary.append({k:c[k] for k in ['agent_id','role','summary','decision','required_revisions','findings','revisions','checks']})
 outstanding={}
 for rr in s.bundle()['rounds']:
  for rec in rr['submissions']:
   bb=rec['content'];aid=bb['agent_id']
   for f in bb['findings']:
    key=aid+':'+f['id']
    if f['severity'] in ['major','critical'] and f['status']=='open':outstanding[key]=f
    elif f['status'] in ['resolved','claim-qualified','not-applicable']:outstanding.pop(key,None)
   for i,v in enumerate(bb['required_revisions'],1):outstanding[f"{aid}:round-{rr['snapshot']['round']}:required-revision-{i}"]={'owner':aid,'text':v}
   for v in bb['revisions']:
    if v.get('status') in ['resolved','claim-qualified','not-applicable']:outstanding.pop(v['finding_id'],None)
 dump(R/'public-state.json',{'prior_round':n,'prior_round_sha256':row['round_sha256'],'committed_findings':summary,'outstanding_issues':outstanding,'coordinator_changes':[]})
 print(json.dumps({'round':n,'round_sha256':row['round_sha256'],'decisions':[(x['content']['role'],x['content']['decision']) for x in row['submissions']],'status':s.status()}))
elif cmd=='status': print(json.dumps(NativeRunStore(R/'run').status()))
elif cmd=='final':
 role=sys.argv[2];p=R/'responses'/'final'/(role+'.json')
 response=p.read_text();body=parse_json(response)
 record=seal_record(body,{'tool':'collaboration.followup_task / specialist final audit response','call_id':f'local-log:frontier20261019-final/final-audit/{role}/actual-public-response','context_id':'/root/review_coordinator/'+role,'recorded_at':now(),'synthetic':False,'public_response':response,'response_sha256':bytes_digest(response.encode())})
 q=R/'sealed'/'final';q.mkdir(parents=True,exist_ok=True);dump(q/(role+'.json'),record)
 print(json.dumps(NativeRunStore(R/'run').record_final_audit(record,(B/'manuscript'/'research-draft.md').read_bytes())))
elif cmd=='export':
 bundle=NativeRunStore(R/'run').bundle();dump(R/'review-bundle.json',bundle);print(json.dumps(validate_review_bundle(bundle,(B/'manuscript'/'research-draft.md').read_bytes()),indent=2))
