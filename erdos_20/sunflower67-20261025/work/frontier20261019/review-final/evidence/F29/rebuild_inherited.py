#!/usr/bin/env python3
"""Rebuild the inherited A1K source closure, then the new proof closure.
Mathlib and Lean dependencies remain pinned, retained caches.
"""
import argparse,hashlib,json,os,pathlib,re,subprocess,time

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lean',required=True)
    ap.add_argument('--packages-root',required=True)
    ap.add_argument('--output',required=True)
    args=ap.parse_args();root=pathlib.Path(__file__).resolve().parent
    output=pathlib.Path(args.output).resolve()
    if output.exists():raise RuntimeError('Fresh output required')
    manifest=json.loads((root/'source-manifest.json').read_text())
    for rel,h in manifest.items():
        if digest(root/rel)!=h:raise RuntimeError('Source mismatch '+rel)
    pkgroot=pathlib.Path(args.packages_root).resolve();paths=[]
    for p in json.loads((root/'lake-manifest.json').read_text())['packages']:
        pkg=pkgroot/p['name']
        got=subprocess.run(['git','-C',str(pkg),'rev-parse','HEAD'],capture_output=True,text=True,check=True).stdout.strip()
        if got!=p['rev']:raise RuntimeError('Dependency revision mismatch '+p['name'])
        paths.append(str(pkg/'.lake/build/lib/lean'))
    graph={}
    def visit(m):
        if m in graph:return
        src=root/(m.replace('.','/')+'.lean')
        if not src.exists():return
        deps=re.findall(r'^import ([\w.]+)',src.read_text(),re.M);graph[m]=deps
        for d in deps:visit(d)
    visit('FrontierAudit')
    inherited={m:[d for d in deps if d.startswith('SunflowerLean.')] for m,deps in graph.items() if m.startswith('SunflowerLean.')}
    order=[]
    while len(order)<len(inherited):
        ready=[m for m in inherited if m not in order and all(d in order for d in inherited[m])]
        if not ready:raise RuntimeError('Cycle or missing inherited import')
        order.extend(ready)
    output.mkdir(parents=True);build=output/'base-build';build.mkdir()
    logs=output/'base-logs';logs.mkdir()
    env=dict(os.environ);env['LEAN_PATH']=os.pathsep.join([str(build),*paths])
    startall=time.monotonic();records=[]
    for i,m in enumerate(order):
        if time.monotonic()-startall>3600:raise RuntimeError('Inherited-rebuild budget exhausted')
        rel=pathlib.Path(m.replace('.','/')+'.lean');src=root/rel;before=digest(src)
        target=(build/rel).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
        cmd=[args.lean,'-o',str(target),str(rel)];start=time.monotonic()
        run=subprocess.run(cmd,cwd=root,env=env,capture_output=True,text=True,timeout=600)
        rec={'module':m,'source_sha256':before,'source_stable':digest(src)==before,
             'command':cmd,'exit_code':run.returncode,'seconds':round(time.monotonic()-start,3),
             'output':run.stdout+run.stderr}
        (logs/(m+'.json')).write_text(json.dumps(rec,indent=2));records.append(rec)
        print(f'{i+1}/{len(order)}',m,run.returncode,rec['seconds'],flush=True)
        if run.returncode or not rec['source_stable']:raise RuntimeError('Inherited module failed '+m)
    base={'status':'pass','module_count':len(records),'modules':order,'seconds':round(time.monotonic()-startall,3),
          'source_manifest_sha256':digest(root/'source-manifest.json'),
          'driver_sha256':digest(pathlib.Path(__file__)),
          'limitation':'All root-reachable A1K source rebuilt. Lean/mathlib/package caches remain; not a full clean-kernel replay.'}
    (output/'base-summary.json').write_text(json.dumps(base,indent=2))
    cmd=['python3',str(root/'replay.py'),'--lean',args.lean,'--base-lib',str(build),'--base-source',str(root),
         '--packages-root',str(pkgroot),'--output',str(output/'new-closure')]
    subprocess.run(cmd,check=True)
    print('SOURCE-CLOSURE REBUILD PASS',flush=True)

if __name__=='__main__':main()
