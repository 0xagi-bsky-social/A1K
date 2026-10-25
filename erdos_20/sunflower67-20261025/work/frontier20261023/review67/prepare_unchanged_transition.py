"""Preserve a completed no-required-revision round before the next input freeze.

This never records a review or creates a judgment. Use only after root has read
all actual responses and the native store has committed the complete round.
"""
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, '/home/user/.codex/skills/superresearch-x2/scripts')
from native_research import NativeRunStore

b = Path(__file__).resolve().parent
bundle = NativeRunStore(b / 'run').bundle()
row = bundle['rounds'][-1]
n = len(bundle['rounds'])
if any(s['content']['required_revisions'] for s in row['submissions']):
    raise ValueError('Required revisions need a specific author response, not this helper')
if hashlib.sha256((b / 'manuscript.md').read_bytes()).hexdigest() != row['snapshot']['manuscript_sha256']:
    raise ValueError('Manuscript changed; use a specific author response')
p = b / f'author-response-r{n}.md'
with p.open('x') as f:
    f.write(f'''# Author response after complete round {n}

All {12*n} actual specialist submissions through round {n} are committed. The latest commitment is {row['round_sha256']}.

No new required revision was entered in this complete round. The author retains the exact manuscript bytes for the next phase; this is a production decision, not a replacement reviewer judgment. The full findings and scope qualifications remain in the committed history. Earlier issues are resolved only where their original reviewer actually supplied a resolution.

The ordinary proof, essential external H27 import and its historical-run and returned-tree limitations, shared model builders, scoped Lean arithmetic, bounded literature search and same-environment agent dependence remain disclosed. A review count is not proof of correctness, independent certification or a full replay. No final audit or publication approval is inferred.
''')
e = json.loads((b / 'evidence.json').read_text())
identity = f'round{n}-committed'
if any(x['id'] == identity for x in e):
    raise ValueError('Evidence identity already exists')
source = (b / 'public' / f'round{n:02d}' / 'committed.json').resolve()
e.append(dict(id=identity, kind='actual-review',
    description=f'Twelve actual round{n} specialist responses', locator=str(source),
    content_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    method='Read complete actual committed responses and their bounded source/check observations.',
    status='limited', limitations=['Same-environment autonomous review; no independent human certification or universal correctness guarantee.']))
(b / 'evidence.json').write_text(json.dumps(e, indent=2)+'\n')
print(json.dumps({'prepared_after_round': n, 'manuscript_unchanged': True}))
