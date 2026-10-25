"""Create a fresh review-only preview; never a final publication or judgment."""
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, '/home/user/.codex/skills/superresearch-x2/scripts')
from native_publication import render_html, _pdf_validation
from render_report import renderer
from markdown_it import MarkdownIt

base = Path(__file__).resolve().parent
number = int(sys.argv[1])
if not 1 <= number <= 99:
    raise ValueError('Invalid preview number')
dest = base / 'previews' / f'round{number:02d}'
dest.mkdir(exist_ok=False)
raw = (base / 'manuscript.md').read_bytes()
sha = hashlib.sha256(raw).hexdigest()
html, title, limitations = render_html(raw, {
    'source-manuscript-sha256': sha, 'review-preview-only': 'true'})
(dest / 'preview.html').write_bytes(html)
receipt = renderer(html, raw, title, dest / 'preview.pdf')
receipt['validation'] = _pdf_validation(dest / 'preview.pdf', title, html)
md = MarkdownIt('commonmark', {'html': False}).enable('table')
links = [child.attrGet('href') for token in md.parse(raw.decode())
         for child in token.children or [] if child.type == 'link_open']
if not links or any(not url.startswith('https://') for url in links):
    raise ValueError('Unexpected source link')
receipt.update(preview_only=True, manuscript_sha256=sha,
    html_limitations=limitations,
    source_link_check={'count': len(links), 'urls': links},
    pdf_sha256=hashlib.sha256((dest / 'preview.pdf').read_bytes()).hexdigest(),
    html_sha256=hashlib.sha256(html).hexdigest(),
    renderer_source_sha256=hashlib.sha256((base / 'render_report.py').read_bytes()).hexdigest(),
    native_validation_scope_note='Generic library MathML label does not establish semantic mathematics tagging; this document uses literal Unicode. No tagged PDF or accessibility assurance.')
(dest / 'render-receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps({'preview': str(dest), 'manuscript': sha, 'validation': receipt['validation']}))
