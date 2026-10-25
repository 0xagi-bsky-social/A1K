#!/usr/bin/env python3
"""Run one bounded independent order68 fibre reconstruction, with hash receipts.

Prepared only: no invocation has been made by its author. This command compiles
and executes only the new edge-partition C++ source, never the Oct20 producer.
One k at a time; optional profile slices are explicitly partial results.
A successful independent deletion-cover receipt is required as input.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
OLD = HERE.parents[1]/'frontier20261020/prior-art68/analysis'
CPP_SHA = 'fa29e7cd616b68a3df3d2252397e30ebc3e6593c5c3d66f2720874d2c9002991'
COVER_CHECKER_SHA = 'b2c164d3110bab41355784f013182eccfd54dffcd6ef55421e129ade51d1bd04'
COVER_BRIDGE_SHA = '77dac237fa1861d05f18d4c07790712049046b9362bcd320f98979be10159093'
OLD_PINS = {
 'prior68_fibre_probe.cpp':'d27445e1db4a8134ac0a3dc28b87c69101b9575c271525206dce6c2ef91b4f40',
 'prior68_fibre_probe.txt':'0181409d2f6e1d978ad87a8356caa60272563e043ca699704981ff2a399a5867',
 'prior68-research.md':'92caa67b0215e80b64b19f25b3d2ba8873f489fb9edc5d389ab3a23d79a9f912',
 'prior68_cover_probe.py':'13c5468d86b8033cf2ef03811845108f9da7a95d31196590a5cef5bd57c4de37',
 'prior68_cover_probe.json':'66b23589dd87a39a5b2e68d2f71a685b97c46a2fb9f7d992398772916e9bf592',
}
EXPECTED = {3:(543,33912),4:(1541,87790),5:(103,2621),6:(1,0)}


def require(condition,message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run(args):
    started=time.monotonic()
    tracked={}
    def bind(path, expected=None):
        path=Path(path).resolve();actual=digest(path)
        require(expected is None or actual==expected,'Dependency hash differs: '+str(path))
        tracked[str(path)]=actual
        return {'path':str(path),'sha256':actual}
    out={'schema':'d16-independent-fibre-replay-v1','status':'FAIL',
         'replayer_sha256':digest(__file__),'k':args.k,
         'assurance':'Independent exact finite reconstruction with an ordinary arbitrary-support cover bridge and explicit imported graph/local theorems; not Lean or an unconditional global extremal proof.'}
    try:
        require(0<args.seconds<=60,'Whole invocation deadline must be in(0,60] seconds')
        require(args.first_profile>=0 and args.profile_count>=0,'Profile slice must be nonnegative')
        out['frozen_diagnostic_dependencies']={name:bind(OLD/name,sha) for name,sha in OLD_PINS.items()}
        cpp=HERE/'d16_fibre_reconstruction.cpp'
        out['independent_source']=bind(cpp,CPP_SHA)
        out['cover_checker']=bind(HERE/'replay_d16_i8_deletion_covers.py',COVER_CHECKER_SHA)
        out['cover_ordinary_bridge']=bind(HERE/'D16-I8-deletion-cover-reconstruction.md',COVER_BRIDGE_SHA)
        out['cover_receipt']=bind(args.cover_receipt)
        cover=json.loads(args.cover_receipt.read_text())
        require(cover.get('schema')=='d16-i8-deletion-cover-exact-reconstruction-v1'
                and cover.get('status')=='PASS' and cover.get('source_sha256')==COVER_CHECKER_SHA,
                'A successful pinned independent cover reconstruction is required')
        require(cover.get('model_count')==8 and cover.get('omission_cases')==5576
                and cover.get('capacities')==[1,2,4,10] and cover.get('pair_count_improvements')==6,
                'Cover receipt has wrong finite domain or capacities')
        require(cover.get('premises',{}).get('ambient_support_cutoff') is None
                and cover.get('premises',{}).get('ambient_global_triple_codegree_cap')==2,
                'Cover receipt has incompatible arbitrary-support premises')
        require(isinstance(cover.get('all_case_cover_lists_sha256'),str)
                and re.fullmatch('[0-9a-f]{64}',cover['all_case_cover_lists_sha256']),
                'Cover receipt lacks a full case commitment')
        for item in cover.get('dependencies',[]):
            bind(item['path'],item['sha256'])
        summary={}
        pattern=re.compile(r'SUMMARY k=(\d+) profiles=(\d+) stars=(\d+) alpha-excluded=(\d+) cover-excluded=(\d+) unresolved=(\d+) minB=(\d+) minUnresolvedB=(\d+)')
        for line in (OLD/'prior68_fibre_probe.txt').read_text().splitlines():
            match=pattern.fullmatch(line)
            require(match is not None,'Unexpected frozen fibre output line')
            k,p,s,alpha,c,unresolved,mb,mub=map(int,match.groups())
            require(k not in summary and EXPECTED.get(k)==(p,s) and alpha==unresolved==0,
                    'Frozen diagnostic domain or result differs')
            summary[k]={'profiles':p,'stars':s,'alpha_excluded':alpha,'unresolved':unresolved}
        require(set(summary)==set(EXPECTED),'Incomplete frozen diagnostic summary')
        out['old_output_scope']='The saved bytes match pinned diagnostic summaries; their original execution is not rerun or independently established by reading them.'
        compiler=shutil.which('g++')
        require(compiler is not None,'g++ is unavailable')
        def remaining():
            return max(0.0,args.seconds-(time.monotonic()-started))
        with tempfile.TemporaryDirectory(prefix='d16-fibre-replay-') as temp:
            executable=Path(temp)/'independent-fibres'
            require(remaining()>0,'Deadline expired before compilation')
            compile_result=subprocess.run([compiler,'-O2','-std=c++17',str(cpp),'-o',str(executable)],
                                          text=True,capture_output=True,timeout=remaining())
            require(compile_result.returncode==0,'Compilation failed: '+compile_result.stderr[-4000:])
            out['compiler']=compiler
            out['compiled_binary_sha256']=digest(executable)
            require(remaining()>0,'Deadline expired after compilation')
            program=subprocess.run([str(executable),str(args.k),str(remaining()),
                                    str(args.first_profile),str(args.profile_count)],
                                   text=True,capture_output=True,timeout=remaining())
            out['program_exit_code']=program.returncode
            out['program_stderr']=program.stderr[-4000:]
            require(program.returncode in (0,3),'Independent reconstruction failed: '+program.stderr[-2000:])
            result=json.loads(program.stdout)
        require(result.get('schema')=='d16-fibre-edge-partition-census-v1'
                and result.get('k')==args.k,'Wrong new reconstruction result')
        require(result.get('profile_total')==EXPECTED[args.k][0],'Profile reconstruction total differs')
        first,stop=result['first_profile'],result['stop_profile']
        rows=result.get('profiles')
        require(isinstance(rows,list) and len(rows)==stop-first
                and [r['index'] for r in rows]==list(range(first,stop)),
                'Profile reconstruction has a gap or duplicate')
        require(sum(r['stars'] for r in rows)==result['stars']
                and sum(r['unresolved'] for r in rows)==result['unresolved'],
                'New summary does not match its per-profile records')
        require(sum(result['excluded_by_cap'])+result['unresolved']==result['stars'],
                'Not every reconstructed star received an outcome')
        if result['complete_k_domain']:
            require(first==0 and stop==EXPECTED[args.k][0]
                    and result['stars']==EXPECTED[args.k][1],
                    'Full domain counts disagree with the target census')
        else:
            require(first>0 or stop<EXPECTED[args.k][0],'Partial domain tag is incorrect')
        out['reconstruction']=result
        require(result['unresolved']==0 and program.returncode==0,'A necessary star vector remains unresolved')
        for path,sha in tracked.items():
            require(digest(path)==sha,'Bound input changed during reconstruction: '+path)
        out['all_bound_inputs_unchanged']=True
        out['status']='PASS' if result['complete_k_domain'] else 'PARTIAL_PASS'
        out['complete_conditional_k_exclusion']=bool(result['complete_k_domain'])
        out['literal_premises']={
            'family_size':68,'SF4_simple_empty_core_forbidden':True,
            'H27_independence_cap':27,'actual_neighbourhood_upper':44,
            'actual_point_star_size':16,'exact_singleton_upper':8,
            'complete_R16_absent':'imported R61 at mu>=41 and Delta<=18',
            'non_R16_link':'B4 separated I8+I8 with only shared Q8 leaves',
            'Jin_image':'surjective A_k, k in3..6; stated ordinary deletion map',
            'cover_capacities':[1,2,4,10],'ambient_support_cutoff':None}
    except Exception as exc:
        out['error']=type(exc).__name__+': '+str(exc)
    out['seconds']=time.monotonic()-started
    return out


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--k',type=int,choices=tuple(EXPECTED),required=True)
    ap.add_argument('--cover-receipt',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--seconds',type=float,default=30)
    ap.add_argument('--first-profile',type=int,default=0)
    ap.add_argument('--profile-count',type=int,default=0)
    args=ap.parse_args()
    if args.output.exists():
        ap.error('Output exists; refusing to overwrite a reconstruction')
    result=run(args)
    with args.output.open('x') as file:
        json.dump(result,file,indent=2,sort_keys=True);file.write('\n')
    summary=result.get('reconstruction',{})
    print(json.dumps({'status':result['status'],'k':args.k,'profiles':len(summary.get('profiles',[])),
                      'stars':summary.get('stars'),'unresolved':summary.get('unresolved'),
                      'seconds':result['seconds'],'output':str(args.output),'error':result.get('error')}))
    return 0 if result['status'] in ('PASS','PARTIAL_PASS') else 1

if __name__=='__main__':
    raise SystemExit(main())
