#!/usr/bin/env python3
"""Bounded D17 v6 exterior discovery, with explicit staged producer antecedents.

One fresh process per case, immutable receipts, LP limit20s/process90s.
This records discovery only; exact replay and independent coverage are separate.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
OUT = HERE / 'degree17_full'
V4 = 'a1beae56f60205a48442a1c6a31d2148557443511fb119a1936ffda8578bebf2'
V6 = '8f43465ef15e09ba5ea8f472a4382f844ccb3ebeface8841f7963625f65e8138'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def strict(d):
    q = d.get('dual', {})
    return bool(q.get('below51') or q.get('below0'))


def bound(p):
    return dict(path=str(p), sha256=sha(p))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--kind', required=True)
    ap.add_argument('--stage', choices=['E4', 'E3'], required=True)
    args = ap.parse_args()
    source = HERE / 'degree17_full_projection_v6.py'
    if sha(source) != V6:
        raise ValueError('Frozen source changed')
    spec = importlib.util.spec_from_file_location('catalogue_only', source)
    model = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(model)
    allowed = ['P9-P8-i1', 'P9-P8-i2']
    if args.kind not in allowed:
        raise ValueError('This driver only accepts the eight independently staged candidate types')
    cat = model.marker_catalogue(args.kind)
    forbidden = []
    yprior = None
    if args.kind.startswith('P9-'):
        p = OUT / 'P9-IY-active-v2-replayed-manifest.json'
        d = json.loads(p.read_text())
        if not d.get('exact_replays_bound') or d['active_case_count'] != 12:
            raise ValueError('Missing Y coverage')
        forbidden = sorted({s for r in d['internal_orbits'] for s in r['orbit']})
        if len(forbidden) != 15:
            raise ValueError('Wrong Y exclusion count')
        yprior = bound(p)
    # Take the first strict stage for each Z-internal orbit. Check later-stage
    # forbidden masks come entirely from earlier strict stage0 orbits.
    internals, closed0 = [], set()
    pending = []
    for case, orbit in cat.items():
        if orbit['category'] != 'internal-Z':
            continue
        matches = list(OUT.glob(f'{args.kind}-{case}-internal-Z-stage0-v4-*.json'))
        matches = [p for p in matches if not p.stem.endswith('-phaseone')]
        if len(matches) != 1:
            raise ValueError('Missing or ambiguous stage0')
        p = matches[0]
        if p.with_name(p.stem + '-phaseone.json').exists():
            p = p.with_name(p.stem + '-phaseone.json')
        d = json.loads(p.read_text())
        if not (d['source_sha256'] == V4 and d['forbidden'] == forbidden and
                d['kind'] == args.kind and d['case'] == case and
                not d['empty_z'] and d['assigned_z'] is None and
                not d['forbid_four_core'] and d.get('h27_cliques') is None):
            raise ValueError('Wrong internal stage0 premises')
        if strict(d):
            internals.append(dict(case=case, stage=0, **bound(p)))
            closed0.update(orbit['orbit'])
        else:
            pending.append(case)
    for case in pending:
        matches = list(OUT.glob(f'{args.kind}-{case}-internal-Z-stage1-v4-*.json'))
        if len(matches) != 1:
            raise ValueError('Missing or ambiguous stage1')
        p = matches[0]
        d = json.loads(p.read_text())
        if not (d['source_sha256'] == V4 and d['kind'] == args.kind and
                d['case'] == case and set(d['forbidden']) == closed0 | set(forbidden)
                and not d['empty_z'] and d['assigned_z'] is None and
                not d['forbid_four_core'] and d.get('h27_cliques') is None and strict(d)):
            raise ValueError('Unclosed internal stage1 or wrong premises')
        internals.append(dict(case=case, stage=1, **bound(p)))
    four_prior = None
    if args.stage == 'E3':
        p = OUT / f'{args.kind}-exterior-E4-v6-progress.json'
        d = json.loads(p.read_text())
        if not (d['completed'] == d['total'] and d['all_completed_strict']):
            raise ValueError('Four-core discovery stage not complete')
        for r in d['records']:
            q = Path(r['path'])
            if sha(q) != r['sha256'] or not strict(json.loads(q.read_text())):
                raise ValueError('Four-core antecedent changed')
        four_prior = bound(p)
    category = {'E4': 'mixed-four-core', 'E3': 'mixed-three-core-plus-exterior'}[args.stage]
    cases = [c for c, r in cat.items() if r['category'] == category]
    label = 'exterior-' + args.stage + '-v6'
    env = dict(os.environ, OPENBLAS_NUM_THREADS='1', PYTHONDONTWRITEBYTECODE='1')
    records = []
    for case in cases:
        matches = [p for p in OUT.glob(f'{args.kind}-{case}-{label}-*.json')
                   if not p.stem.endswith('-phaseone')]
        if not matches:
            cmd = [sys.executable, str(source), '--kind', args.kind, '--case', case,
                   '--solve', '--seconds', '20', '--empty-z', '--label', label,
                   '--forbidden', json.dumps(forbidden)]
            if args.stage == 'E3':
                cmd.append('--forbid-four-core')
            subprocess.run(cmd, check=True, timeout=90, env=env)
            matches = [p for p in OUT.glob(f'{args.kind}-{case}-{label}-*.json')
                       if not p.stem.endswith('-phaseone')]
        if len(matches) != 1:
            raise ValueError('Ambiguous exterior receipt')
        p = matches[0]
        d = json.loads(p.read_text())
        if not (d['source_sha256'] == V6 and d['kind'] == args.kind and d['case'] == case
                and d['forbidden'] == forbidden and d['empty_z'] and d['assigned_z'] is None
                and d['forbid_four_core'] == (args.stage == 'E3') and
                d.get('h27_cliques') is None):
            raise ValueError('Wrong exterior premises')
        if d['status'] == 2:
            phase = p.with_name(p.stem + '-phaseone.json')
            if not phase.exists():
                subprocess.run([sys.executable, str(HERE / 'degree17_full_phaseone_v6.py'),
                                '--receipt', str(p), '--seconds', '20'],
                               check=True, timeout=60, env=env)
            p = phase
            d = json.loads(p.read_text())
        records.append(dict(case=case, status=d['status'], strict_diagnostic=strict(d),
                            upper=d.get('dual', {}).get('display'), **bound(p)))
        progress = dict(kind=args.kind, stage=args.stage, completed=len(records),
                        total=len(cases), source_sha256=V6, Y_antecedent=yprior,
                        internal_antecedents=internals, four_core_antecedent=four_prior,
                        records=records, all_completed_strict=all(r['strict_diagnostic'] for r in records),
                        assurance='Producer diagnostics only; exact replay and independent coverage separate.')
        (OUT / f'{args.kind}-exterior-{args.stage}-v6-progress.json').write_text(json.dumps(progress, indent=2) + '\n')
        print(json.dumps(dict(kind=args.kind, stage=args.stage, completed=len(records),
                              total=len(cases), case=case, strict_diagnostic=strict(d))), flush=True)


if __name__ == '__main__':
    main()
