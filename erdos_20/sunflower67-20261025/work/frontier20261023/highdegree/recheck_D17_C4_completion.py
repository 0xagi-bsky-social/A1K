#!/usr/bin/env python3
"""Small independent mask reconstruction; imports no template checker/model.

Only literal template consequences are checked. Universal classification and
the separated high-link17 theorem remain explicit ordinary imports.
"""
from hashlib import sha256
from itertools import combinations, permutations
import json
from pathlib import Path
from time import monotonic

HERE = Path(__file__).resolve().parent
CERT = HERE.parents[1] / 'frontier20261020/prior-art68/repository/companion/terminal/r16/results/seven_certificate.json'
PINNED = {
    CERT: 'fe172301b201819c029d9a1b7e8931f516cbd90aa978977118b7853b2ead7164',
    HERE / 'D17-C4-internal-completion.md': '47d39e647d8e4c14864de262c46ce576d08a12f66b046d51af6554476efabd77',
    HERE / 'check_D17_C4_completion.py': 'a1dfbf89fd0a992c3ab87ff600a374af2703673d61b01b78a960d6d52d8d5f88',
    HERE / 'D17-C4-completion-literal.json': 'f4b74d3743d8ae5664ac2fd8aec7b125080bf315f37885ea00112c129d2e18b9',
}


def require(test, message):
    if not test:
        raise ValueError(message)


def mask(points):
    return sum(1 << v for v in points)


def points(m):
    return [v for v in range(m.bit_length()) if m & (1 << v)]


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def record_key(row):
    return (row['template'], row['point'], tuple(row['neighbours']),
            tuple(map(tuple, row['edges'])), tuple(map(tuple, row['completions'])))


def main():
    started = monotonic()
    for path, expected in PINNED.items():
        require(digest(path) == expected, f'Changed input: {path.name}')
    cert = json.loads(CERT.read_text())
    require([r['id'] for r in cert['rows']] == list(range(8)), 'I7 domain mismatch')
    models = [(f'H{r["id"]}', frozenset(mask(t) for t in r['blocks']))
              for r in cert['rows']]
    # Independent literal P10 and hub/triad construction of Q8.
    p10 = frozenset(mask(map(int, t)) for t in
                    '012 015 023 034 045 124 134 135 235 245'.split())
    models.append(('P10', p10))
    blocks = sorted(p10, key=lambda m: tuple(points(m)))
    for count, prefix in [(1, 'P9'), (2, 'P8')]:
        models.extend((f'{prefix}-{j:02d}', p10 - set(removed))
                      for j, removed in enumerate(combinations(blocks, count)))
    q8 = {mask((hub,) + pair) for hub in (0, 1)
          for pair in combinations((2, 3, 4), 2)}
    q8.update(mask((0, 1, leaf)) for leaf in (5, 6))
    models.append(('Q8', frozenset(q8)))
    records = []
    checked_points = 0
    for name, L in models:
        require(all(t.bit_count() == 3 for t in L), 'Bad rank')
        require(all(a & b for a, b in combinations(L, 2)), 'Not intersecting')
        require(all(not (a & b == b & c == a & c)
                    for a, b, c in combinations(L, 3)), 'Literal sunflower')
        support = 0
        for t in L:
            support |= t
        for v in points(support):
            checked_points += 1
            edges = {t ^ (1 << v) for t in L if t & (1 << v)}
            if len(edges) != 4:
                continue
            neighbour_mask = 0
            for e in edges:
                neighbour_mask |= e
            neighbours = points(neighbour_mask)
            if len(neighbours) != 4:
                continue
            # Recognize C4 by an actual cyclic ordering, rather than a degree list.
            is_cycle = any(edges == {mask((order[i], order[(i+1) % 4]))
                                     for i in range(4)}
                           for order in permutations(neighbours))
            if not is_cycle:
                continue
            completions = sorted(points(t) for t in L if not t & ~neighbour_mask)
            require(completions, f'Missing completion at {name}/{v}')
            records.append(dict(template=name, point=v, neighbours=neighbours,
                                edges=sorted(points(e) for e in edges),
                                completions=completions))
    saved = json.loads((HERE / 'D17-C4-completion-literal.json').read_text())
    require(len(models) == saved['models'] == 65, 'Model count mismatch')
    require(checked_points == saved['points_checked'] == 392, 'Point count mismatch')
    require(len(records) == 8, 'Wrong C4 domain')
    require(sorted(map(record_key, records)) == sorted(map(record_key, saved['C4_points'])),
            'Saved literal records differ')
    require(saved['source_sha256'] == PINNED[HERE / 'check_D17_C4_completion.py'],
            'Original source commitment differs')
    require(saved['ordinary_bridge_sha256'] == PINNED[HERE / 'D17-C4-internal-completion.md'],
            'Original bridge commitment differs')
    for path, expected in PINNED.items():
        require(digest(path) == expected, 'Input changed during check')
    receipt = dict(status='PASS_INDEPENDENT_LITERAL_C4_RECONSTRUCTION',
                   model_count=len(models), point_count=checked_points,
                   C4_points=records, seconds=monotonic()-started,
                   source_sha256=digest(Path(__file__)),
                   inputs={str(p): h for p, h in PINNED.items()},
                   assurance='Literal catalogue consequence only. Arbitrary-support I7/I8 completeness and separated high-link17 are ordinary imports; no solver or Lean.')
    output = HERE / 'D17-C4-independent-reconstruction.json'
    with output.open('x') as f:
        json.dump(receipt, f, indent=2)
        f.write('\n')
    print(json.dumps({k: receipt[k] for k in ('status', 'model_count', 'point_count', 'seconds')}))


if __name__ == '__main__':
    main()
