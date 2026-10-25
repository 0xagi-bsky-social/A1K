#!/usr/bin/env python3
"""Bounded serial D17 internal-Z discovery; every child has a fresh process.

Uses frozen v4, no optional H27 rows. On P9 branches the independently
covered/replayed IY exclusions are explicit antecedents. Producer diagnostics
do not replace the model bridge, staged coverage, or solver-free replay.
Existing hash-matched receipts are reused; uncertain/failed outputs preserved.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import os
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
SOURCE_SHA = 'a1beae56f60205a48442a1c6a31d2148557443511fb119a1936ffda8578bebf2'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--kind', required=True)
    args = ap.parse_args()
    source = HERE / 'degree17_full_projection_v4.py'
    if sha(source) != SOURCE_SHA:
        raise ValueError('Frozen v4 changed')
    spec = importlib.util.spec_from_file_location('catalogue_only_v4', source)
    model = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(model)
    if args.kind not in model.KINDS or args.kind == 'P10-H0':
        raise ValueError('Choose a remaining D17 root type')
    forbidden = []
    antecedent = None
    if args.kind.startswith('P9-'):
        antecedent = HERE / 'degree17_full/P9-IY-active-v2-replayed-manifest.json'
        prior = json.loads(antecedent.read_text())
        if not prior.get('exact_replays_bound') or prior['active_case_count'] != 12:
            raise ValueError('Missing twelve-case IY coverage with exact replay binding')
        forbidden = sorted({t for r in prior['internal_orbits'] for t in r['orbit']})
        if len(forbidden) != 15:
            raise ValueError('Incomplete Y-internal exclusion')
    cases = [case for case, row in model.marker_catalogue(args.kind).items()
             if row['category'] == 'internal-Z']
    records = []
    env = dict(os.environ, OPENBLAS_NUM_THREADS='1', PYTHONDONTWRITEBYTECODE='1')
    label = 'internal-Z-stage0-v4'
    for case in cases:
        matches = list((HERE / 'degree17_full').glob(f'{args.kind}-{case}-{label}-*.json'))
        originals = [p for p in matches if not p.stem.endswith('-phaseone')]
        if not originals:
            subprocess.run([sys.executable, str(source), '--kind', args.kind,
                            '--case', case, '--solve', '--seconds', '20',
                            '--label', label, '--forbidden', json.dumps(forbidden)],
                           check=True, timeout=90, env=env)
            originals = [p for p in (HERE / 'degree17_full').glob(
                f'{args.kind}-{case}-{label}-*.json') if not p.stem.endswith('-phaseone')]
        if len(originals) != 1:
            raise ValueError('Ambiguous discovery receipts')
        path = originals[0]
        record = json.loads(path.read_text())
        if not (record['source_sha256'] == SOURCE_SHA and record['kind'] == args.kind
                and record['case'] == case and record['forbidden'] == forbidden
                and not record['empty_z'] and record['assigned_z'] is None
                and not record['forbid_four_core'] and record.get('h27_cliques') is None):
            raise ValueError('Existing receipt has different premises')
        if record['status'] == 2:
            phase = path.with_name(path.stem + '-phaseone.json')
            if not phase.exists():
                subprocess.run([sys.executable, str(HERE / 'degree17_full_phaseone.py'),
                                '--receipt', str(path), '--seconds', '30'],
                               check=True, timeout=45, env=env)
            record = json.loads(phase.read_text())
            path = phase
        strict = bool(record.get('dual', {}).get('below51') or
                      record.get('dual', {}).get('below0'))
        records.append(dict(case=case, path=str(path), sha256=sha(path),
                            status=record['status'], strict_diagnostic=strict,
                            upper=record.get('dual', {}).get('display')))
        progress = dict(kind=args.kind, completed=len(records), total=len(cases),
                        source_sha256=SOURCE_SHA, records=records,
                        Y_antecedent=None if antecedent is None else
                        dict(path=str(antecedent), sha256=sha(antecedent)),
                        all_completed_strict=all(r['strict_diagnostic'] for r in records),
                        assurance='Producer diagnostics only; no exact replay or branch closure implied.')
        out = HERE / 'degree17_full' / f'{args.kind}-internal-Z-stage0-progress.json'
        out.write_text(json.dumps(progress, indent=2) + '\n')
        print(json.dumps(dict(kind=args.kind, completed=len(records), total=len(cases),
                              case=case, strict_diagnostic=strict)), flush=True)


if __name__ == '__main__':
    main()
