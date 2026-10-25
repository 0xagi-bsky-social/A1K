from pathlib import Path
import sys,json,hashlib,shutil
R=Path(__file__).resolve().parent
sys.path.insert(0,'/home/user/.codex/skills/superresearch-x2/scripts')
from native_research import NativeRunStore
status=NativeRunStore(R/'run').status();assert status['committed_rounds']==9 and status['open_round'] is None
s=json.loads((R/'public-state.json').read_text());assert not s['outstanding_issues']
p=R/'evidence/F38';p.mkdir()
for name in ['reuse-agent-review.json','reuse-computation.json']:shutil.copyfile(R/'analysis/round-09/copyeditor'/name,p/name)
shutil.copyfile(R/'evidence/F32/copyeditor-reuse.py',p/'copyeditor-reuse.py')
a=json.loads((p/'reuse-agent-review.json').read_text());m=hashlib.sha256((R.parent/'manuscript/research-draft.md').read_bytes()).hexdigest();assert a['manuscript_sha256']==m
entry={'id':'F38','kind':'final-bounded-text-comparison','description':'Actual round9 comparison of exact final v6 manuscript; adjacent computation and executable script approved evidence','locator':str(p/'reuse-agent-review.json'),'method':'Agent-executed normalized exact-token comparison and explicit classification of all matches','status':'limited','limitations':['Only accessible F16/F17 source excerpt segments; no human review, semantic-paraphrase detection, comprehensive originality or priority certification'],'content_sha256':hashlib.sha256((p/'reuse-agent-review.json').read_bytes()).hexdigest()}
e=json.loads((R/'evidence.json').read_text());e.append(entry);(R/'evidence.json').write_text(json.dumps(e,indent=2)+'\n')
v=json.loads((R/'verification.json').read_text())
for x in v:
 if x['scope']=='facts':x['method']='Actual final rounds 1–9 compared theorem statements, primary-source claims, compiler receipts, exact arithmetic and final rendering repairs'
 if x['scope']=='citations':x['evidence_ids']+=['F35','F37'];x['observations'].append('Round9 citation owner verified repaired preview and planned-release relative-link targets and exact archive identity.')
 if x['scope']=='logic':x['evidence_ids'].append('F35');x['observations'].append('Round9 actual checks confirmed exhaustive small-L branches, preserved formula signs and correct counterexample selection/relabeling.')
 if x['scope']=='text_reuse':
  x['method']='Copyeditor executed a fresh comparison of the exact final v6 manuscript and inspected every reported match in round9'
  x['observations']=['Only three occurrences of the cited nine-token paper title met the eight-token threshold across accessible F16/F17 excerpts; final manuscript digest bound by F38.']
  x['limitations']=['No human review, broad originality/semantic-paraphrase service, or unprovided-source comparison.']
  x['evidence_ids']=['F16','F17','F38']
(R/'verification.json').write_text(json.dumps(v,indent=2)+'\n')
s['coordinator_changes']=['No manuscript or renderer change after round9. Appended the real exact-final-byte text comparison as F38 and updated scoped verification observations from actual completed reviews.'];(R/'public-state.json').write_text(json.dumps(s,indent=2)+'\n')
print(json.dumps({'manuscript_sha256':m,'outstanding_issues':0,'new_evidence':'F38'}))
