from pathlib import Path
import json, sys, hashlib, shutil
from datetime import datetime, timezone
sys.path.insert(0, '/home/user/.codex/skills/superresearch-x2/scripts')
from native_research import NativeRunStore, load_json, parse_json, seal_record, bytes_digest, validate_review_bundle
R = Path(__file__).resolve().parent
B = R.parent
def dump(p, v):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(v, indent=2, ensure_ascii=False) + '\n')
def now(): return datetime.now(timezone.utc).isoformat()
def resume(extra=''):
    s=NativeRunStore(R/'run').status()
    participation=[]
    for r in load_json(R/'roster.json'):
        participation.append({
            'role':r['role'],'context_id':r['context_id'],
            'sealed_round_responses':sorted(x.parent.name for x in (R/'sealed').glob('round-*/'+r['role']+'.json')),
            'final_audit_file':(R/'sealed'/'final'/(r['role']+'.json')).exists()
        })
    dump(R/'participation.json',participation)
    (R/'RESUME.md').write_text(
        '# Actual specialist review resume\n\n'
        'Run: frontier20261020-boundary80-final-review. Coordinator context: /root/review80_coordinator.\n'
        'Twelve role contexts in roster.json are actual fresh fork_turns=none contexts. Reuse them with followup_task. '
        'While this coordinator is active, at most two reviewers can run. After round4 handoff and coordinator idleness, root may run three reviewers. '
        'Never share uncommitted sibling output. Only committed public state is shared.\n'
        'Use manage.py open N, record N ROLE, commit, final ROLE, export. Responses are actual specialist-authored JSON; never fabricate any.\n\n'
        +json.dumps(s,indent=2)+'\n\n'+extra+'\n')
cmd=sys.argv[1]
if cmd=='create':
    NativeRunStore.create(R/'run',load_json(R/'contract.json'),load_json(R/'roster.json'),limitations=[
        'Actual separate collaboration contexts in one orchestration environment; model/provider details unavailable; organizational independence not established',
        'Local unsigned hashes and declared actual tool provenance; no third-party authentication or independent human certification',
        'Bounded primary-source and accessible text comparison; no exhaustive novelty or originality claim'])
    resume('Ready to open round 1.')
elif cmd=='open':
    n=int(sys.argv[2]); p=R/'public'/f'round-{n:02d}'; p.mkdir(parents=True)
    shutil.copyfile(B/'manuscript'/'research-draft.md',p/'manuscript.md')
    state=load_json(R/'public-state.json') if (R/'public-state.json').exists() else {
        'review_status':'First genuine review after actual A/B exclusions and axiom-audited I27 to G80.',
        'coordinator_changes':['Normalized public banner and display math before first freeze'],
        'pending_evidence':['Source-closure rebuild is running; do not infer completed coverage.']}
    ret=NativeRunStore(R/'run').open_round((p/'manuscript.md').read_bytes(),load_json(R/'evidence.json'),load_json(R/'verification.json'),state)
    dump(p/'snapshot.json',ret)
    shutil.copyfile(R/'contract.json',p/'contract.json')
    shutil.copyfile(R/'roster.json',p/'roster.json')
    resume('Current frozen public input: '+str(p)+'.')
    print(json.dumps({'round':n,'snapshot_sha256':ret['snapshot_sha256'],'manuscript_sha256':ret['snapshot']['manuscript_sha256'],'directory':str(p)}))
elif cmd=='record':
    n=int(sys.argv[2]); role=sys.argv[3]; p=R/'responses'/f'round-{n:02d}'/(role+'.json')
    response=p.read_text(); body=parse_json(response)
    context=next(x['context_id'] for x in load_json(R/'roster.json') if x['role']==role)
    record=seal_record(body,{'tool':'collaboration.followup_task; specialist-authored public JSON file and actual completion message',
        'call_id':f'local-log:frontier20261020-boundary80/round-{n:02d}/{role}/actual-public-response',
        'context_id':context,'recorded_at':now(),'synthetic':False,'public_response':response,'response_sha256':bytes_digest(response.encode())})
    dump(R/'sealed'/f'round-{n:02d}'/(role+'.json'),record)
    print(json.dumps(NativeRunStore(R/'run').record_submission(record)))
    resume()
elif cmd=='commit':
    s=NativeRunStore(R/'run'); row=s.commit_round(); n=row['snapshot']['round']
    dump(R/'committed'/f'round-{n:02d}.json',row)
    summary=[]
    for x in row['submissions']:
        c=x['content']; summary.append({k:c[k] for k in ['agent_id','role','summary','decision','required_revisions','findings','revisions','checks']})
    outstanding={}
    for rr in s.bundle()['rounds']:
        for rec in rr['submissions']:
            b=rec['content']; aid=b['agent_id']
            for f in b['findings']:
                key=aid+':'+f['id']
                if f['severity'] in ['major','critical'] and f['status']=='open': outstanding[key]=f
                elif f['status'] in ['resolved','claim-qualified','not-applicable']: outstanding.pop(key,None)
            for i,v in enumerate(b['required_revisions'],1):
                outstanding[f"{aid}:round-{rr['snapshot']['round']}:required-revision-{i}"]={'owner':aid,'text':v}
            for v in b['revisions']:
                if v.get('status') in ['resolved','claim-qualified','not-applicable']: outstanding.pop(v['finding_id'],None)
    dump(R/'public-state.json',{'prior_round':n,'prior_round_sha256':row['round_sha256'],'committed_findings':summary,'outstanding_issues':outstanding,'coordinator_changes':[]})
    resume('Round '+str(n)+' committed. Root must receive revision requests before next freeze. Findings in public-state.json.')
    print(json.dumps({'round':n,'round_sha256':row['round_sha256'],'decisions':[(x['content']['role'],x['content']['decision']) for x in row['submissions']],'outstanding_issues':outstanding,'status':s.status()}))
elif cmd=='status': print(json.dumps(NativeRunStore(R/'run').status()))
elif cmd=='final':
    role=sys.argv[2]; p=R/'responses'/'final'/(role+'.json')
    response=p.read_text(); body=parse_json(response)
    context=next(x['context_id'] for x in load_json(R/'roster.json') if x['role']==role)
    record=seal_record(body,{'tool':'collaboration.followup_task; specialist-authored final audit JSON and actual completion message',
        'call_id':f'local-log:frontier20261020-boundary80/final-audit/{role}/actual-public-response',
        'context_id':context,'recorded_at':now(),'synthetic':False,'public_response':response,'response_sha256':bytes_digest(response.encode())})
    dump(R/'sealed'/'final'/(role+'.json'),record)
    print(json.dumps(NativeRunStore(R/'run').record_final_audit(record,(B/'manuscript'/'research-draft.md').read_bytes())))
    resume()
elif cmd=='export':
    bundle=NativeRunStore(R/'run').bundle(); dump(R/'review-bundle.json',bundle)
    result=validate_review_bundle(bundle,(B/'manuscript'/'research-draft.md').read_bytes())
    dump(R/'validation.json',result); print(json.dumps(result,indent=2)); resume()
