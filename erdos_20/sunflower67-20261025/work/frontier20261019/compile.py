import os,sys,pathlib,json,subprocess,time,hashlib,concurrent.futures,fcntl
base=pathlib.Path(__file__).resolve().parent
cfg=json.loads((base/'runtime.json').read_text())
root=base/'lean'; out=base/'build'; out.mkdir(exist_ok=True)
env=dict(os.environ);env['LEAN_PATH']=':'.join([str(out),*cfg['package_paths']])
mode=sys.argv[1] if len(sys.argv)>1 else 'all'
def compile_file(p):
 rel=p.relative_to(root); target=out/rel.with_suffix('.olean'); target.parent.mkdir(parents=True,exist_ok=True)
 start=time.monotonic(); source_before=p.read_bytes()
 with (base/'lean.lock').open('w') as lock:
  fcntl.flock(lock,fcntl.LOCK_EX)
  r=subprocess.run([cfg['lean'],'-o',str(target),str(rel)],cwd=root,env=env,capture_output=True,text=True)
 rec={'file':str(rel),'source_sha256':hashlib.sha256(source_before).hexdigest(),'source_stable':source_before==p.read_bytes(),'exit_code':r.returncode,'seconds':round(time.monotonic()-start,3),'output':r.stdout+r.stderr}
 (base/'logs'/str(rel).replace('/','__')).with_suffix('.json').write_text(json.dumps(rec,indent=2))
 return rec
if mode=='all':
 files={str(p.relative_to(root).with_suffix('')).replace('/','.'):p for p in (root/'SunflowerLean').glob('*.lean')}
 deps={m:{line.split()[1] for line in p.read_text().splitlines() if line.startswith('import ') and line.split()[1] in files} for m,p in files.items()}
 done=set(); records=[]
 while len(done)<len(files):
  ready=[m for m in files if m not in done and deps[m]<=done]
  if not ready: raise RuntimeError('Import cycle')
  with concurrent.futures.ThreadPoolExecutor(max_workers=1) as pool:
   for m,rec in zip(ready,pool.map(compile_file,[files[m] for m in ready])):
    records.append(rec); print(m,rec['exit_code'],rec['seconds'],flush=True)
    if rec['exit_code']: print(rec['output'],flush=True);sys.exit(rec['exit_code'])
    done.add(m)
 (base/'base-build.json').write_text(json.dumps(records,indent=2))
else:
 env['LEAN_PATH']=':'.join(['/home/user/Documents/Codex/2026-09-22/you-ve-been-interrupted-unexpectedly-please/work/erdos20-v13/lean/.lake/build/lib/lean', str(out), *cfg['package_paths']])
 r=compile_file(root/mode);print(r['output']);print('EXIT',r['exit_code'],'SECONDS',r['seconds']);sys.exit(r['exit_code'])
