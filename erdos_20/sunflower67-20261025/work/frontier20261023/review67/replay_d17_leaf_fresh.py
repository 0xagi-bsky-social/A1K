"""Invoke the frozen exact D17 replay into a new reviewer-owned output.

The mathematical evaluator is unchanged. This wrapper exists because the
original CLI deliberately refuses to overwrite the archived replay path.
It neither runs a solver nor upgrades the shared-builder assurance boundary.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPLAYER = HERE.parent/'highdegree'/'replay_degree17_full_v9.py'
PIN = '10304e6fa2f3adfea9de387e82601ee6eef7f445b9460e35827d2e2eced634c8'

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('receipt',type=Path)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    if hashlib.sha256(REPLAYER.read_bytes()).hexdigest()!=PIN:
        raise ValueError('Frozen replay evaluator changed')
    os.environ['OPENBLAS_NUM_THREADS']='1'
    sys.path.insert(0,str(REPLAYER.parent))
    spec=importlib.util.spec_from_file_location('frozen_d17_replay',REPLAYER)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    result=module.replay(args.receipt.resolve(),30,'auto')
    # Preserve the evaluator result literally; wrapper metadata is separate.
    with args.output.open('x') as f:
        json.dump(result,f,indent=2,allow_nan=False)
        f.write('\n')
    exact=result.get('exact_replay',{})
    print(json.dumps({'result':result['result'],'strict_exclusion':exact.get('strict_exclusion'),
        'output':str(args.output.resolve()),'seconds':result.get('seconds'),
        'error':result.get('error')}))
    return 0 if result['result']=='PASS' and exact.get('strict_exclusion') is True else 1

if __name__=='__main__':
    raise SystemExit(main())
