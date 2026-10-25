from pathlib import Path
import sys,json,hashlib
sys.path.insert(0,'/home/user/.codex/skills/superresearch-x2/scripts')
from native_publication import render_html,render_pdf
R=Path(__file__).resolve().parent
b=(R/'manuscript/research-draft.md').read_bytes();h=hashlib.sha256(b).hexdigest()
P=R/'preview'/h[:12];P.mkdir(parents=True,exist_ok=True)
(P/'manuscript.md').write_bytes(b)
v=render_html(b)
print(type(v),flush=True)
if isinstance(v,tuple):print([type(x).__name__ for x in v],flush=True)
else:print(str(v)[:300],flush=True)
if isinstance(v,tuple):html,title,limitations=v
else:raise RuntimeError('Unexpected HTMLreturn')
(P/'report.html').write_bytes(html)
out=render_pdf(html,b,title,P/'report.pdf',python_executable='/home/user/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3')
(P/'rendering.json').write_text(json.dumps({'source_sha256':h,'title':title,'html_limitations':limitations,'pdf':out},indent=2))
print(json.dumps(out,indent=2),flush=True)
