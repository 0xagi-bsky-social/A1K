#!/usr/bin/env python3
"""Schedule P9-Q8 exterior v9 discovery from an explicit replayed proof plan.

Prepared source only; not executed during preparation. Before any LP, the
standard-library coverage checker validates every prior receipt/replay and
reconstructs its literal marker ancestry. Each requested case gets one fresh
bounded solver process, then at most one phase-one process if needed.
Discovery outputs do not become antecedents until separately replayed and
included in a new explicit plan. No automatic E4-to-E3 promotion occurs.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
OUT = HERE / 'degree17_full'
V9 = '31368d8392328daa9f161b23e40ef7c3df3d9acd4743cf4914f9df0215b74eb2'
PHASE = 'a38b7f30dbdcc54f2452d540f019bcb22f2823fd61c2d8925180c36ca00c6f70'
CHECKER = 'e8553f1726e58d30032294c4e96711a1c3507d4cb381ad532982c1a4003f805b'


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def bind(path):
    return dict(path=str(Path(path).resolve()), sha256=sha(path))


def strict(data):
    q = data.get('dual', {})
    z = data.get('certificate_kind') == 'zero-infeasibility'
    v = [q.get(k) for k in ('scale','H','correction','upper_numerator')]
    return (data.get('status') == 0 and all(type(t) is int for t in v)
            and v[0] > 0 and v[3] == v[1]+v[2]
            and v[3] < (0 if z else 51*v[0])
            and q.get('below0' if z else 'below51') is True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--plan', type=Path, required=True,
                    help='Explicit plan with all8 IZ leaves; E3 also needs all E4 leaves')
    ap.add_argument('--stage', choices=['E4','E3'], required=True)
    selection = ap.add_mutually_exclusive_group(required=True)
    selection.add_argument('--case')
    selection.add_argument('--all', action='store_true')
    ap.add_argument('--seconds', type=int, default=20)
    args = ap.parse_args()
    require(1 <= args.seconds <= 30, 'Per-solver limit must lie in1..30 seconds')
    source, phase, checker_path = (HERE/'degree17_full_projection_v9.py',
        HERE/'degree17_full_phaseone_v9.py', HERE/'check_d17_stage_plan_v9.py')
    require(sha(source) == V9 and sha(phase) == PHASE and sha(checker_path) == CHECKER,
            'Frozen model, phase-one producer or stage checker changed')
    plan_bound = bind(args.plan)
    plan = json.loads(args.plan.read_text())
    require(plan.get('kind') == 'P9-Q8' and not plan.get('unproved_candidates'),
            'Wrong kind or unproved candidate in antecedent plan')
    spec = importlib.util.spec_from_file_location('literal_stage_only', checker_path)
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    def timeout(_signum, _frame):
        raise TimeoutError('Thirty-second literal prerequisite inspection expired')
    signal.signal(signal.SIGALRM, timeout)
    signal.setitimer(signal.ITIMER_REAL, 30)
    prior = checker.check(args.plan, allow_partial=True)
    cert = json.loads((checker.PRIOR / 'repository/companion/terminal/r16/results/seven_certificate.json').read_text())
    g = checker.reconstruct('P9-Q8', cert)
    signal.setitimer(signal.ITIMER_REAL, 0)
    require(not prior['direct_unmarked_exclusion'], 'Kind is already directly excluded')
    require(g['y_four'] | g['z_four'] <= set(prior['absent_core_four']),
            'Complete Y and Z internal exclusions have not been justified')
    if args.stage == 'E3':
        require(g['all_four'] <= set(prior['absent_core_four']),
                'E3 requires replayed complete E4 coverage, not producer counters')
    category = {'E4':'mixed-four-core','E3':'mixed-three-core-plus-exterior'}[args.stage]
    cases = sorted(c for c,r in g['records'].items() if r['category'] == category)
    require(len(cases) == (58 if args.stage == 'E4' else 24), 'Unexpected literal Q8 orbit census')
    requested = cases if args.all else [args.case]
    require(all(c in cases for c in requested), 'Requested case is outside this stage')
    forbidden = sorted(g['y_four'])
    label = 'exterior-' + args.stage + '-v9'
    env = dict(os.environ, OPENBLAS_NUM_THREADS='1', OMP_NUM_THREADS='1',
               MKL_NUM_THREADS='1', PYTHONDONTWRITEBYTECODE='1')
    progress_path = OUT / f'P9-Q8-exterior-{args.stage}-v9-progress.json'
    records = {}
    if progress_path.exists():
        old = json.loads(progress_path.read_text())
        require(old.get('kind') == 'P9-Q8' and old.get('stage') == args.stage
                and old.get('source_sha256') == V9
                and old.get('antecedent_plan') == plan_bound,
                'Existing progress binds a different stage or plan')
        for record in old['records']:
            require(record['case'] in cases and record['case'] not in records,
                    'Duplicate or alien progress case')
            require(sha(record['path']) == record['sha256'], 'Changed earlier discovery receipt')
            records[record['case']] = record
    for case in requested:
        pattern = f'P9-Q8-{case}-{label}-*.json'
        matches = [p for p in OUT.glob(pattern) if not p.stem.endswith('-phaseone')]
        if not matches:
            cmd = [sys.executable, str(source), '--kind','P9-Q8','--case',case,
                   '--solve','--seconds',str(args.seconds),'--empty-z',
                   '--label',label,'--forbidden',json.dumps(forbidden)]
            if args.stage == 'E3':
                cmd.append('--forbid-four-core')
            subprocess.run(cmd, check=True, timeout=90, env=env)
            matches = [p for p in OUT.glob(pattern) if not p.stem.endswith('-phaseone')]
        require(len(matches) == 1, 'Missing or ambiguous immutable exterior receipt')
        p = matches[0]
        d = json.loads(p.read_text())
        require(d.get('source_sha256') == V9 and d.get('kind') == 'P9-Q8'
                and d.get('case') == case and d.get('forbidden') == forbidden
                and d.get('empty_z') is True and d.get('assigned_z') is None
                and d.get('forbid_four_core') == (args.stage == 'E3')
                and d.get('extra_members') == [] and d.get('h27_cliques') is None
                and d.get('crowding_imports') is True
                and d.get('degree_distributions') is False,
                'Exterior receipt has unexpected actual-member or trace premises')
        if d.get('status') == 2:
            active = p.with_name(p.stem + '-phaseone.json')
            if not active.exists():
                subprocess.run([sys.executable,str(phase),'--receipt',str(p),
                                '--seconds',str(args.seconds)],
                               check=True, timeout=60, env=env)
            original = d
            d = json.loads(active.read_text())
            require(d.get('certificate_kind') == 'zero-infeasibility'
                    and d.get('input_receipt_sha256') == sha(p)
                    and d.get('source_sha256') == V9
                    and d.get('premise_sha256') == original['premise_sha256']
                    and d.get('certificate_producer_sha256') == PHASE,
                    'Phase-one output does not bind the exact exterior model')
            p = active
        record = dict(case=case, status=d['status'], strict_diagnostic=strict(d),
                      upper=d.get('dual',{}).get('display'), **bind(p))
        if case in records:
            require(record == records[case], 'Existing progress disagrees with its receipt')
        records[case] = record
        state = dict(kind='P9-Q8', stage=args.stage, source_sha256=V9,
                     completed=len(records), total=len(cases),
                     antecedent_plan=plan_bound, coverage_checker=bind(checker_path),
                     all_internal_orbits_explicit=True,
                     records=[records[c] for c in cases if c in records],
                     all_completed_strict=all(r['strict_diagnostic'] for r in records.values()),
                     assurance='Discovery diagnostics only. Prior leaves bound by exact replay and literal stage inspection; new leaves require their own replay and coverage.')
        progress_path.write_text(json.dumps(state,indent=2)+'\n')
        print(json.dumps(dict(case=case, completed=len(records), total=len(cases),
                              strict_diagnostic=strict(d), path=str(p))),flush=True)
        require(sha(args.plan) == plan_bound['sha256'] and sha(source) == V9,
                'Plan or model changed during scheduling')
        if not strict(d):
            print(json.dumps(dict(stopped=True, reason='Nonstrict or unfinished case; no later stage promoted')),
                  flush=True)
            break


if __name__ == '__main__':
    main()
