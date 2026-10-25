from pathlib import Path
import sys,json,hashlib,subprocess,shutil
sys.path.insert(0,'/home/user/.codex/skills/superresearch-x2/scripts')
from native_publication import _pdf_validation
from render_local import renderer,render_html_local as render_html
R=Path(__file__).resolve().parent
p=R/'preview'/sys.argv[1];p.mkdir(parents=True)
m=(R.parent/'manuscript/research-draft.md').read_bytes()
h,t,lim=render_html(m);(p/'report.html').write_bytes(h)
r=renderer(h,m,t,p/'report.pdf');r['validation']=_pdf_validation(p/'report.pdf',t,h)
(p/'receipt.json').write_text(json.dumps({'manuscript_sha256':hashlib.sha256(m).hexdigest(),'html_limits':lim,'pdf':r},indent=2)+'\n')
shutil.copyfile(R/'render_local.py',p/'render_local.py')
subprocess.run(['pdftoppm','-png','-r','85',str(p/'report.pdf'),str(p/'page')],check=True,capture_output=True)
files={x.name:{'path':str(x),'sha256':hashlib.sha256(x.read_bytes()).hexdigest(),'bytes':x.stat().st_size} for x in sorted(p.iterdir()) if x.is_file()}
(p/'manifest.json').write_text(json.dumps({'manuscript_sha256':hashlib.sha256(m).hexdigest(),'files':files},indent=2)+'\n')
print(json.dumps({'path':str(p),'pages':r['validation']['page_count'],'manuscript_sha256':hashlib.sha256(m).hexdigest()}))
