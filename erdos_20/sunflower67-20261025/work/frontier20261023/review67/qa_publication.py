"""Check actual published bytes and prepare pages for separate visual inspection.

Does not certify visual inspection or manufacture scientific review.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

sys.path.insert(0, '/home/user/.codex/skills/superresearch-x2/scripts')
from native_research import validate_review_bundle

b = Path(__file__).resolve().parent
name = sys.argv[1]
if re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9._-]{2,95}', name) is None:
    raise ValueError('Invalid bundle name')
d = b / 'publication' / name
audit = b / 'publication-audits' / name
receipt = json.loads((b / 'publication' / (name+'.publication.json')).read_text())
bundle = json.loads((audit / 'review-bundle.json').read_text())
raw = (d / 'report.md').read_bytes()
validation = validate_review_bundle(bundle, raw)
if not validation.get('valid') or not validation.get('publication_eligible'):
    raise ValueError('Review validation failed')
if receipt['status'] != 'published' or set(p.name for p in d.iterdir()) != {'report.md','report.html','report.pdf'}:
    raise ValueError('Three complete formats required')
if raw != (b / 'manuscript.md').read_bytes():
    raise ValueError('Reviewed manuscript differs')
for filename, record in receipt['artifacts'].items():
    data = (d / filename).read_bytes()
    if hashlib.sha256(data).hexdigest() != record['sha256'] or len(data) != record['bytes']:
        raise ValueError('Artifact commitment mismatch: '+filename)
if receipt['review_bundle_sha256'] != validation['bundle_sha256']:
    raise ValueError('Review bundle commitment mismatch')
pages = audit / 'visual-pages'
pages.mkdir(exist_ok=False)
subprocess.run(['pdftoppm', '-r', '90', '-png', str(d/'report.pdf'), str(pages/'page')], check=True, timeout=45)
images = sorted(pages.glob('page-*.png'))
if len(images) != receipt['renderer']['validation']['page_count']:
    raise ValueError('Incomplete page rendering')
result = dict(actual_review_validation=validation, exact_three_formats=True,
    artifact_hashes_match=True, source_bytes_match=True,
    rendered_pages=[str(p) for p in images], visual_inspection='NOT YET PERFORMED',
    scope_note='Literal Unicode mathematics; the generic native MathML label does not establish semantic math tagging, accessibility conformance or visual equivalence. Page inspection must be separately recorded.')
with (audit/'byte-and-page-qa.json').open('x') as f:
    json.dump(result, f, indent=2); f.write('\n')
print(json.dumps({'status':'actual-bytes-and-page-count-checked','pages':len(images),
    'submission_count':validation['submission_count'],'visual_pages':str(pages)}))
