from pathlib import Path
import sys,json,hashlib
sys.path.insert(0,'/home/user/.codex/skills/superresearch-x2/scripts')
from native_publication import render_html,_pdf_validation
from render_report import renderer
R=Path(__file__).resolve().parent;b=(Path(sys.argv[1]) if len(sys.argv)>1 else R/'manuscript/research-draft.md').read_bytes();h=hashlib.sha256(b).hexdigest();P=R/'preview'/(h[:12]+('-'+sys.argv[2] if len(sys.argv)>2 else ''));P.mkdir(exist_ok=True,parents=True)
(P/'manuscript.md').write_bytes(b)
html,title,limitations=render_html(b);(P/'report.html').write_bytes(html)
r=renderer(html,b,title,P/'report.pdf')
r['validation']=_pdf_validation(P/'report.pdf',title,html)
(P/'custom-rendering.json').write_text(json.dumps({'source_sha256':h,'html_limitations':limitations,'pdf':r},indent=2))
print(str(P));print(json.dumps(r,indent=2))
