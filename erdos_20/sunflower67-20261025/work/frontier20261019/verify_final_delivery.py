"""Root-side read-only verification of the final local delivery.

Run only after actual review and publication. This records neither reviews nor
acceptances and does not promote review provenance to independent certification.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import sys
import zipfile
from html.parser import HTMLParser

ROOT = Path(__file__).resolve().parents[2]
WORK = ROOT / 'work/frontier20261019'
OUT = ROOT / 'outputs/frontier20261019'
sys.path.insert(0, '/home/user/.codex/skills/superresearch-x2/scripts')
from native_research import validate_review_bundle


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read_json(path):
    return json.loads(path.read_text())


class MetaParser(HTMLParser):
    def __init__(self):
        super().__init__()
        self.metadata = {}

    def handle_starttag(self, tag, attributes):
        if tag == 'meta':
            attrs = dict(attributes)
            if 'name' in attrs and 'content' in attrs:
                self.metadata[attrs['name']] = attrs['content']


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--preview', type=Path, required=True,
                        help='The exact final reviewer-approved preview directory')
    args = parser.parse_args()
    review = WORK / 'review-final'
    report = OUT / 'research-report'
    manuscript = (report / 'report.md').read_bytes()
    bundle = read_json(OUT / 'research-review-bundle.json')
    verdict = validate_review_bundle(bundle, manuscript)
    assert verdict['valid'] and verdict['publication_eligible'], verdict
    roster = {entry['role'] for entry in bundle['roster']}
    assert len(roster) == 12
    assert len(bundle['rounds']) >= 10
    for row in bundle['rounds']:
        submissions = row['submissions']
        assert len(submissions) == 12
        assert {s['content']['role'] for s in submissions} == roster
    finals = bundle['final_audit']
    assert len(finals) == 3
    assert {s['content']['role'] for s in finals} == {'chief', 'alpha', 'beta'}
    assert all(s['content']['decision'] == 'accept' for s in finals)
    assert all(s['content']['manuscript_sha256'] == sha(manuscript) for s in finals)
    assert manuscript == (WORK / 'manuscript/research-draft.md').read_bytes()
    assert bundle == read_json(review / 'review-bundle.json')

    published = read_json(review / 'publication-return.json')
    assert published['status'] == 'published'
    assert published == read_json(OUT / 'research-report.publication.json')
    actual = {
        p.name: {'sha256': sha(p.read_bytes()), 'bytes': p.stat().st_size}
        for p in sorted(report.iterdir()) if p.is_file()
    }
    assert actual == published['artifacts']
    assert all(actual[name]['bytes'] > 0 for name in ('report.md', 'report.html', 'report.pdf'))
    html_metadata = MetaParser()
    html_metadata.feed((report / 'report.html').read_text())
    assert html_metadata.metadata['native-manuscript-sha256'] == sha(manuscript)
    assert html_metadata.metadata['native-review-bundle-sha256'] == verdict['bundle_sha256']
    assert html_metadata.metadata['native-contract-sha256'] == verdict['contract_sha256']
    html_without_commitments = re.sub(
        r'<meta name="native-(?:manuscript|review-bundle|contract)-sha256" content="[0-9a-f]{64}">',
        '', (report / 'report.html').read_text())
    assert html_without_commitments == (args.preview / 'report.html').read_text()
    preview = read_json(args.preview / 'manifest.json')
    assert preview['manuscript_sha256'] == sha(manuscript)
    preview_path = (args.preview / 'manifest.json').resolve()
    preview_evidence = [
        item for item in bundle['rounds'][-1]['snapshot']['evidence']
        if item.get('locator') == str(preview_path)
    ]
    assert len(preview_evidence) == 1
    assert preview_evidence[0]['content_sha256'] == sha(preview_path.read_bytes())
    for item in preview['files'].values():
        actual_preview_file = Path(item['path'])
        assert sha(actual_preview_file.read_bytes()) == item['sha256']
        assert actual_preview_file.stat().st_size == item['bytes']
    rendered_pages = sorted((review / 'published-render').glob('page-*.png'))
    expected_pages = {name for name in preview['files'] if name.startswith('page-') and name.endswith('.png')}
    assert expected_pages
    assert {p.name for p in rendered_pages} == expected_pages
    assert all(sha(p.read_bytes()) == preview['files'][p.name]['sha256'] for p in rendered_pages)

    formal_delivery = read_json(OUT / 'formal-delivery.json')
    archive = OUT / 'formal-source-and-receipts.zip'
    assert sha(archive.read_bytes()) == formal_delivery['sha256']
    assert archive.stat().st_size == formal_delivery['bytes']
    with zipfile.ZipFile(archive) as z:
        assert z.testzip() is None
        assert not any(name.endswith(('.olean', '.ilean', '.o')) for name in z.namelist())
        source_index = json.loads(z.read('archive-file-hashes.json'))
        # Manifest keys are relative to the packaged formal/ directory.
        indexed_archive_names = {'formal/' + name for name in source_index}
        assert set(z.namelist()) == indexed_archive_names | {'archive-file-hashes.json'}
        assert len(source_index) == formal_delivery['source_and_receipt_files']
        assert all(sha(z.read('formal/' + name)) == digest for name, digest in source_index.items())
    source = read_json(OUT / 'formal/source-rebuild-receipt/summary.json')
    assert source['status'] == 'pass'
    assert (source['inherited_A1K_modules_rebuilt'], source['new_modules_rebuilt'], source['named_roots_audited']) == (100, 14, 66)
    result = {
        'status': 'pass',
        'review_validation': verdict,
        'complete_rounds': len(bundle['rounds']),
        'actual_recorded_submissions': sum(len(r['submissions']) for r in bundle['rounds']),
        'final_acceptances': 3,
        'manuscript_sha256': sha(manuscript),
        'actual_artifacts': actual,
        'published_pages_equal_reviewed_preview': len(rendered_pages),
        'published_html_equals_reviewed_preview_except_commitments': True,
        'formal_archive_sha256': sha(archive.read_bytes()),
        'formal_assurance': source['assurance'],
        'limitations': [
            'Same controller and host; no independent human certification.',
            'Review provenance is local declared tool provenance, not cryptographic agent authentication.',
            'Lean and pinned mathlib/third-party package caches were not rebuilt in a clean environment.'
        ]
    }
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
