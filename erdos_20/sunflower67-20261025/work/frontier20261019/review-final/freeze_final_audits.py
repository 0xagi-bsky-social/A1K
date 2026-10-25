from pathlib import Path
import sys,json,hashlib,shutil
sys.path.insert(0,'/home/user/.codex/skills/superresearch-x2/scripts')
from native_research import NativeRunStore
R=Path(__file__).resolve().parent
b=NativeRunStore(R/'run').bundle()
assert len(b['rounds'])>=10
last=b['rounds'][-1];s=last['snapshot'];m=(R.parent/'manuscript/research-draft.md').read_bytes()
assert hashlib.sha256(m).hexdigest()==s['manuscript_sha256']
p=R/'public/final';p.mkdir()
(p/'manuscript.md').write_bytes(m)
(p/'snapshot.json').write_text(json.dumps({'snapshot':s,'snapshot_sha256':last['snapshot_sha256']},indent=2)+'\n')
bindings={k:s[k] for k in ['manuscript_sha256','evidence_sha256','verification_sha256']};bindings['round_sha256']=last['round_sha256'];bindings['submission_count']=sum(len(x['submissions']) for x in b['rounds']);bindings['round_count']=len(b['rounds'])
(p/'bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
history=[{'round':row['snapshot']['round'],'phase':row['snapshot']['phase'],'round_sha256':row['round_sha256'],'manuscript_sha256':row['snapshot']['manuscript_sha256'],'submissions':[x['content'] for x in row['submissions']]} for row in b['rounds']]
(p/'history.json').write_text(json.dumps(history,indent=2)+'\n')
shutil.copyfile(R/'public-state.json',p/'final-public-state.json')
(p/'record-locators.json').write_text(json.dumps({'full_committed_records':[str(R/'committed'/f'round-{i:02d}.json') for i in range(1,len(b['rounds'])+1)],'roster':b['roster'],'limitations':b['limitations']},indent=2)+'\n')
print(json.dumps(bindings))
