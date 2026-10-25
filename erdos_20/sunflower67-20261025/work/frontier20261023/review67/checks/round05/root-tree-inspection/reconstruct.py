"""Reconstruct the returned Git trees; this does not establish completeness."""
import hashlib
import json
from pathlib import Path
import subprocess

BASE = Path(__file__).resolve().parents[3]
source = BASE / 'research-r4/h27-tree-tool-result.json'
response = json.loads(source.read_text())
tree = json.loads(response['value']['result']['structuredContent']['content'])
entries = tree['tree']
results = []
for prefix, expected in [('', tree['sha'])] + [
    (e['path'], e['sha']) for e in entries if e['type'] == 'tree'
]:
    children = [dict(e, name=e['path'].rsplit('/', 1)[-1])
                for e in entries if e['path'].rpartition('/')[0] == prefix]
    children.sort(key=lambda e: (e['name'] + ('/' if e['type'] == 'tree' else '')).encode())
    payload = b''.join((str(int(e['mode'])) + ' ' + e['name']).encode()
                       + b'\0' + bytes.fromhex(e['sha']) for e in children)
    digest = hashlib.sha1(b'tree ' + str(len(payload)).encode() + b'\0' + payload).hexdigest()
    row = dict(path=prefix or '/', expected=expected, computed=digest,
               matches=digest == expected, children=len(children))
    if not prefix:
        row['git_hash_object'] = subprocess.run(
            ['git', 'hash-object', '-t', 'tree', '--stdin'], input=payload,
            capture_output=True, check=True).stdout.decode().strip()
    results.append(row)
print(json.dumps({'trees': results, 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest()}, indent=2))
