#!/usr/bin/env python3
"""Rebuild the new proof closure in an empty output directory against pinned caches.
This is not a clean rebuild of Lean, mathlib, or the inherited A1K dependency cache.
"""
import argparse, hashlib, json, os, pathlib, re, subprocess, sys, time

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lean',required=True)
    ap.add_argument('--base-lib',required=True,help='Retained A1K build/lib/lean directory')
    ap.add_argument('--base-source',required=True,help='A1K source root containing SunflowerLean')
    ap.add_argument('--packages-root',required=True,help='Pinned .lake/packages directory')
    ap.add_argument('--output',required=True,help='Fresh nonexistent receipt/build directory')
    args=ap.parse_args()
    root=pathlib.Path(__file__).resolve().parent
    output=pathlib.Path(args.output).resolve()
    if output.exists(): raise RuntimeError('Output must not already exist')
    manifest=json.loads((root/'source-manifest.json').read_text())
    for rel,h in manifest.items():
        if sha(root/rel)!=h: raise RuntimeError('Source hash mismatch: '+rel)
    version=subprocess.run([args.lean,'--version'],capture_output=True,text=True,check=True).stdout.strip()
    if 'version 4.26.0,' not in version: raise RuntimeError('Wrong Lean version: '+version)
    for p in (root/'SunflowerLean').glob('*.lean'):
        q=pathlib.Path(args.base_source)/'SunflowerLean'/p.name
        if not q.exists() or sha(p)!=sha(q): raise RuntimeError('Inherited source mismatch: '+p.name)
    lock=json.loads((root/'lake-manifest.json').read_text())
    paths=[]; deps=[]
    for pkg in lock['packages']:
        p=pathlib.Path(args.packages_root)/pkg['name']
        observed=subprocess.run(['git','-C',str(p),'rev-parse','HEAD'],capture_output=True,text=True,check=True).stdout.strip()
        if observed!=pkg['rev']: raise RuntimeError('Dependency revision mismatch: '+pkg['name'])
        paths.append(str(p/'.lake/build/lib/lean'))
        deps.append({'name':pkg['name'],'revision':observed})
    spec=json.loads((root/'audit-roots.json').read_text())
    modules=spec['modules']+['FrontierAudit']
    graph={m:[i for i in re.findall(r'^import ([\w.]+)',(root/(m+'.lean')).read_text(),re.M) if i in modules] for m in modules}
    ordered=[]
    while len(ordered)<len(modules):
        ready=[m for m in modules if m not in ordered and all(d in ordered for d in graph[m])]
        if not ready: raise RuntimeError('Cyclic new-module imports')
        ordered.extend(ready)
    output.mkdir(parents=True); build=output/'build';build.mkdir()
    env=dict(os.environ)
    env['LEAN_PATH']=os.pathsep.join([str(pathlib.Path(args.base_lib).resolve()),str(build),*paths])
    receipts=[]
    for m in ordered:
        src=root/(m+'.lean'); before=sha(src)
        command=[args.lean,'-o',str(build/(m+'.olean')),src.name]
        start=time.monotonic()
        run=subprocess.run(command,cwd=root,env=env,capture_output=True,text=True,timeout=600)
        rec={'module':m,'source_sha256':before,'source_stable':sha(src)==before,
             'command':command,'exit_code':run.returncode,'seconds':round(time.monotonic()-start,3),
             'output':run.stdout+run.stderr}
        (output/(m+'.json')).write_text(json.dumps(rec,indent=2))
        receipts.append(rec);print(m,rec['exit_code'],rec['seconds'],flush=True)
        if run.returncode or not rec['source_stable']: raise RuntimeError('Compilation failed: '+m)
    audit=receipts[-1]['output']
    entries=[json.loads(s) for s in re.findall(r'FRONTIER_AXIOM_AUDIT (\{[^\n]*\})',audit)]
    if {e['root'] for e in entries}!=set(spec['roots']): raise RuntimeError('Missing or unexpected audit roots')
    allowed={'propext','Classical.choice','Quot.sound'}
    if any(e['status']!='pass' or not set(e['axioms'])<=allowed for e in entries):
        raise RuntimeError('Disallowed axiom audit')
    summary={'status':'pass','assurance':'axiom-audited','version':version,'dependencies':deps,
             'source_manifest_sha256':sha(root/'source-manifest.json'),'modules':ordered,
             'root_count':len(entries),'roots':entries,'import_graph':graph,
             'independence':'same host and toolchain; new module output directory initially empty',
             'limitation':'Inherited A1K and mathlib objects reused; source revision matches do not authenticate cached objects; not clean-kernel-replayed.'}
    (output/'summary.json').write_text(json.dumps(summary,indent=2))
    print('PASS',len(entries),'axiom-audited roots',flush=True)

if __name__=='__main__':
    main()
