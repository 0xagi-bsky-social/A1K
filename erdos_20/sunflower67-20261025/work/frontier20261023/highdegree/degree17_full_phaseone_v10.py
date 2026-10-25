#!/usr/bin/env python3
"""Bounded numerical producer of an exact zero-objective box contradiction.

The frozen, hash-matched original model is rebuilt without changing premises.
The certificate proves that relaxation infeasible, not its geometric premises.
This v10-only adapter passes the exact selected extra members to build and
checks the recorded actual-member support before rebuilding. Use the separate
replay_degree17_full_v10.py for solver-free exact arithmetic verification.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import signal
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
V10_SHA = 'b5be05901b8cacc6fa324e828a3dbe604428864559988b8c13350517a66dc728'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def produce(path, seconds):
    start = time.monotonic()
    def alarm(*_):
        raise TimeoutError('Whole phase-one deadline expired')
    previous = signal.signal(signal.SIGALRM, alarm)
    signal.setitimer(signal.ITIMER_REAL, seconds)
    original = json.loads(path.read_text())
    record = dict(original)
    record.update(certificate_kind='zero-infeasibility', original_status=original['status'],
                  input_receipt_path=str(path), input_receipt_sha256=sha(path),
                  certificate_producer_sha256=sha(__file__), status=-1,
                  assurance='Numerical discovery plus exact integer-box diagnostic for the unchanged hash-matched necessary relaxation; not Lean or a whole branch proof.')
    record.pop('dual', None)
    record.pop('primal_trace', None)
    try:
        if original['status'] != 2:
            raise ValueError('Only numerical status-2 originals are accepted')
        source = HERE / 'degree17_full_projection_v10.py'
        if original['source_sha256'] != V10_SHA or sha(source) != V10_SHA:
            raise ValueError('This adapter requires the frozen v10 source and a matching receipt')
        spec = importlib.util.spec_from_file_location('p10_phaseone_frozen', source)
        model = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(model)
        if sha(model.LOCAL43) != original['imported_local43_sha256']:
            raise ValueError('local43 source mismatch')
        for item in original.get('imported_crowding_sources', {}).values():
            if sha(item['path']) != item['sha256']:
                raise ValueError('Imported proof dependency hash mismatch')
        keys = ('kind', 'case', 'empty_z', 'assigned_z', 'forbidden', 'forbid_four_core',
                'degree_distributions', 'crowding_imports')
        kwargs = {k: original[k] for k in keys}
        kwargs['extra_members'] = original['extra_members']
        extras, selected, n = model.selected_members(
            original['kind'], original['case'], original['assigned_z'], original['extra_members'])
        if (list(extras) != original['extra_members']
                or list(selected) != original['selected_actual_members']
                or list(range(n)) != original['represented_points']):
            raise ValueError('Extra actual members or represented support differs from the receipt')
        if original.get('h27_cliques') is not None:
            clique = original['h27_cliques']
            if sha(clique['path']) != clique['sha256']:
                raise ValueError('H27 row data changed')
            kwargs.update(h27_cliques=clique['path'], h27_cliques_sha256=clique['sha256'])
        tr, bounds, A, b, E, f, labels, sizes = model.build(**kwargs)
        if (len(bounds) != original['columns'] or len(tr) != original['trace_columns']
                or len(b) != original['upper_rows'] or len(f) != original['equal_rows']
                or sizes != original['catalogue_sizes']):
            raise ValueError('Original model dimensions differ')
        import numpy as np
        from scipy.optimize import linprog
        from scipy.sparse import hstack, vstack, csr_matrix
        stacked = vstack((A, E, -E), format='csr')
        aug = hstack((stacked, csr_matrix(-np.ones((stacked.shape[0], 1)))), format='csr')
        rhs = np.concatenate((b, f, -f))
        objective = np.zeros(len(bounds) + 1)
        objective[-1] = 1
        result = linprog(objective, A_ub=aug, b_ub=rhs, bounds=bounds + [(0, None)],
                         method='highs', options={'time_limit': max(0.01, seconds-(time.monotonic()-start))})
        record.update(status=int(result.status), phase_one_minimum=None if result.fun is None else float(result.fun),
                      message=str(result.message))
        if result.status != 0:
            return record
        scale = 10**10
        weights = [max(0, round(-float(v)*scale)) for v in result.ineqlin.marginals]
        ys = weights[:len(b)]
        ep, en = weights[len(b):len(b)+len(f)], weights[len(b)+len(f):]
        es = [a-b for a,b in zip(ep,en)]
        q, H = [0]*len(bounds), 0
        for mat, rhs0, ws in ((A, b, ys), (E, f, es)):
            for i,w in enumerate(ws):
                if not w:
                    continue
                if not float(rhs0[i]).is_integer():
                    raise ValueError('Noninteger RHS')
                H += w*int(rhs0[i])
                for e in range(mat.indptr[i], mat.indptr[i+1]):
                    if not float(mat.data[e]).is_integer():
                        raise ValueError('Noninteger matrix entry')
                    q[int(mat.indices[e])] += w*int(mat.data[e])
        correction = sum(max(-lo*c, -hi*c) for (lo,hi),c in zip(bounds,q))
        numerator = H+correction
        record['dual'] = dict(objective='zero', scale=scale, H=H, correction=correction,
                              upper_numerator=numerator, below0=numerator<0, display=numerator/scale,
                              inequality_sign='nonnegative weights on A*x<=b',
                              equality_sign='signed weights on E*x=f',
                              ineq=[[i,w,labels[i]] for i,w in enumerate(ys) if w],
                              eq=[[i,w] for i,w in enumerate(es) if w])
        record['phase_one_formulation'] = 'min t with A*x-t<=b, E*x-t<=f, -E*x-t<=-f; original boxes, t>=0. Stored certificate discards t and bounds zero strictly below zero.'
        if sha(path) != record['input_receipt_sha256'] or sha(source) != V10_SHA:
            raise ValueError('Original receipt or v10 source changed during phase one')
        for item in original.get('imported_crowding_sources', {}).values():
            if sha(item['path']) != item['sha256']:
                raise ValueError('Imported proof dependency changed during phase one')
        return record
    except Exception as exc:
        record.update(status=-1, message=f'{type(exc).__name__}: {exc}')
        return record
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, previous)
        record['phase_one_seconds'] = time.monotonic()-start


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--receipt',type=Path,required=True)
    ap.add_argument('--seconds',type=float,default=30)
    args=ap.parse_args()
    if not 0<args.seconds<=30:
        ap.error('Deadline must be in (0,30] seconds')
    path=args.receipt.resolve()
    destination=path.with_name(path.stem+'-phaseone.json')
    if destination.exists():
        raise FileExistsError(destination)
    r=produce(path,args.seconds)
    destination.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps(dict(receipt=str(destination),status=r['status'],
                          gap=r.get('dual',{}).get('upper_numerator'),
                          strict=r.get('dual',{}).get('below0'),seconds=r['phase_one_seconds'])),flush=True)


if __name__=='__main__':
    main()
