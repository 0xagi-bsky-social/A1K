from pathlib import Path
import json,hashlib,shutil,subprocess,sys
R=Path(__file__).resolve().parent
sys.path.insert(0,'/home/user/.codex/skills/superresearch-x2/scripts')
from native_research import NativeRunStore
status=NativeRunStore(R/'run').status()
assert status['committed_rounds']==8 and status['open_round'] is None
M=R.parent/'manuscript/research-draft.md';old=M.read_text();lines=[];changes=[]
for line in old.splitlines(keepends=True):
 new=line
 if not line.startswith('    '):
  for expression in ['L*L-3*L','L*L-6L','S*S-6S','6U-L*L+6L']:
   new=new.replace(expression,'`'+expression+'`')
 if new!=line:changes.append({'old':line.rstrip(),'new':new.rstrip()})
 lines.append(new)
assert len(changes)==3
M.write_text(''.join(lines))
subprocess.run([sys.executable,str(R/'preview_new.py'),'v6'],check=True)
p=R/'preview/v6'
shutil.copyfile(R/'preview/v5/receipt-erratum.json',p/'receipt-erratum.json')
shutil.copyfile(R/'preview/v5/formula-source-changes.json',p/'formula-source-changes.json')
(p/'inline-source-changes.json').write_text(json.dumps(changes,indent=2)+'\n')
# Preview directories mirror the release's relative hyperlink layout.
O=R.parents[2]/'outputs/frontier20261019';target=R/'preview/formal';target.mkdir()
shutil.copyfile(O/'formal/source-manifest.json',target/'source-manifest.json')
shutil.copyfile(O/'formal-source-and-receipts.zip',R/'preview/formal-source-and-receipts.zip')
checks=[]
for ref in ['../formal/source-manifest.json','../formal-source-and-receipts.zip']:
 a=(p/ref).resolve();b=(O/'research-report'/ref).resolve();assert a.is_file() and b.is_file()
 ha=hashlib.sha256(a.read_bytes()).hexdigest();hb=hashlib.sha256(b.read_bytes()).hexdigest();assert ha==hb
 checks.append({'relative_href':ref,'preview_target':str(a),'planned_release_target':str(b),'sha256':ha,'bytes':a.stat().st_size,'both_exist_and_match':True})
q=R/'evidence/F37';q.mkdir()
(q/'link-layout-check.json').write_text(json.dumps({'finding_id':'/root/review_coordinator/citation_verifier:round-8:required-revision-1','checks':checks,'limits':['Filesystem target existence and byte identity; no claim about every PDF viewer handling relative URI annotations.','No report is published before final audit.']},indent=2)+'\n')
files={x.name:{'path':str(x),'sha256':hashlib.sha256(x.read_bytes()).hexdigest(),'bytes':x.stat().st_size} for x in sorted(p.iterdir()) if x.is_file() and x.name!='manifest.json'}
(p/'manifest.json').write_text(json.dumps({'manuscript_sha256':hashlib.sha256(M.read_bytes()).hexdigest(),'files':files},indent=2)+'\n')
e=json.loads((R/'evidence.json').read_text())
def entry(i,kind,desc,loc,method,limits):
 return {'id':i,'kind':kind,'description':desc,'locator':str(loc),'method':method,'status':'limited','limitations':limits,'content_sha256':hashlib.sha256(loc.read_bytes()).hexdigest()}
e.append(entry('F35','rendered-preview','Actual v6 HTML/PDF, eight PNG pages, source changes, mappings, renderer, receipts and erratum; all manifest files approved evidence',p/'manifest.json','Native MathML plus explicit PDF formula mappings; multiplication in inline expressions now protected from Markdown emphasis',['No browser/accessibility conformance certification; source-style math code blocks retained']))
# F36 is intentionally reserved for the real round-8 copyeditor output appended separately.
e.append(entry('F37','delivery-link-layout','Actual preview and planned release relative-link existence/hash comparison; referenced target files approved for read-only integrity verification',q/'link-layout-check.json','Filesystem path resolution and SHA256 equality',['No cross-viewer relative-URI behavior certification; publication gate remains pending']))
(R/'evidence.json').write_text(json.dumps(e,indent=2)+'\n')
s=json.loads((R/'public-state.json').read_text());s['coordinator_changes']=['Protected four inline expressions across three prose lines with code spans; algebra and all six displayed formulas unchanged.','Regenerated v6 preview and staged identical sibling manifest/archive targets for relative preview links; checked the same targets already exist at planned release paths.'];(R/'public-state.json').write_text(json.dumps(s,indent=2)+'\n')
pub=R/'publish_accepted.py';pub.write_text(pub.read_text().replace('preview/v5/manifest.json','preview/v6/manifest.json'))
print(json.dumps({'manuscript_sha256':hashlib.sha256(M.read_bytes()).hexdigest(),'changes':len(changes)}))
