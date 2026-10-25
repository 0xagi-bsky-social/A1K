"""Publish only the actual completed native review; no review generation."""
from pathlib import Path
import sys,json,hashlib,shutil,subprocess
sys.path.insert(0,'/home/user/.codex/skills/superresearch-x2/scripts')
from native_research import validate_review_bundle
import native_publication
from native_publication import publish_local
from render_local import renderer,render_html_local
R=Path(__file__).resolve().parent
PROJECT=R.parents[2]
OUT=PROJECT/'outputs/frontier20261019'
m=(R.parent/'manuscript/research-draft.md').read_bytes()
b=json.loads((R/'review-bundle.json').read_text())
v=validate_review_bundle(b,m)
if not v.get('valid') or not v.get('publication_eligible'): raise RuntimeError(json.dumps(v))
preview=json.loads((R/'preview/v6/manifest.json').read_text())
if preview['manuscript_sha256']!=hashlib.sha256(m).hexdigest(): raise RuntimeError('Final preview needs updating')
if preview['files']['render_local.py']['sha256']!=hashlib.sha256((R/'render_local.py').read_bytes()).hexdigest(): raise RuntimeError('Renderer differs from approved preview')
native_html=native_publication.render_html
def reviewed_html(manuscript,commitments=None):
    native_publication.render_html=native_html
    try:return render_html_local(manuscript,commitments)
    finally:native_publication.render_html=reviewed_html
native_publication.render_html=reviewed_html
receipt=publish_local(b,m,OUT,'research-report',renderer=renderer)
(R/'publication-return.json').write_text(json.dumps(receipt,indent=2)+'\n')
if receipt.get('status')!='published': raise RuntimeError(json.dumps(receipt))
with (OUT/'research-review-bundle.json').open('xb') as target: target.write((R/'review-bundle.json').read_bytes())
qa=R/'published-render';qa.mkdir()
subprocess.run(['pdftoppm','-png','-r','85',str(OUT/'research-report/report.pdf'),str(qa/'page')],check=True,capture_output=True)
comparisons={p.name:hashlib.sha256(p.read_bytes()).hexdigest()==preview['files'].get(p.name,{}).get('sha256') for p in sorted(qa.glob('page-*.png'))}
artifacts={p.name:{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in sorted((OUT/'research-report').iterdir())}
local={'validation':v,'actual_artifacts':artifacts,'artifact_receipt_matches':artifacts==receipt['artifacts'],'preview_pixel_equality':comparisons,'published_markdown_equals_reviewed':(OUT/'research-report/report.md').read_bytes()==m,'review_bundle_file_sha256':hashlib.sha256((OUT/'research-review-bundle.json').read_bytes()).hexdigest(),'review_bundle_canonical_sha256':v['bundle_sha256'],'limitations':['Unsigned local commitments; no organizational independence or human certification','PDF preserves readable source notation; no accessibility-conformance claim']}
(R/'publication-check.json').write_text(json.dumps(local,indent=2)+'\n')
print(json.dumps({'publication':receipt.get('status'),'validation':v,'artifact_receipt_matches':local['artifact_receipt_matches'],'preview_pixel_equality':comparisons,'artifacts':artifacts},indent=2))
