import pathlib,json,os,sys,subprocess,time,hashlib
root=pathlib.Path(__file__).resolve().parent
old=root.parents[1]/'frontier20261019'
cfg=json.loads((old/'runtime.json').read_text())
cwd=root.parents[2]
base=cwd/'outputs/frontier20261019/formal/source-rebuild-receipt/base-build'
cache=pathlib.Path('/home/user/Documents/Codex/2026-09-22/you-ve-been-interrupted-unexpectedly-please/work/erdos20-v13/lean/.lake/build/lib/lean')
(root/'build').mkdir(exist_ok=True);(root/'receipts').mkdir(exist_ok=True)
env=dict(os.environ);env['LEAN_PATH']=':'.join(map(str,[root/'build',root.parent/'formal/build',root.parent/'compute/build',cache,base,*cfg['package_paths']]))
name=sys.argv[1];source=root/name;start=time.monotonic();before=source.read_bytes()
command=[cfg['lean'],'--memory=1024','-o',str(root/'build'/source.with_suffix('.olean').name),name]
try:
 p=subprocess.run(command,cwd=root,env=env,text=True,capture_output=True,timeout=120)
except subprocess.TimeoutExpired as e:
 p=subprocess.CompletedProcess(command,124,(e.stdout or b'').decode() if isinstance(e.stdout,bytes) else (e.stdout or ''),(e.stderr or b'').decode() if isinstance(e.stderr,bytes) else (e.stderr or ''))
r={'source':str(source),'source_sha256':hashlib.sha256(before).hexdigest(),'source_stable':before==source.read_bytes(),'command':command,'LEAN_PATH':env['LEAN_PATH'],'exit_code':p.returncode,'elapsed_seconds':time.monotonic()-start,'output':p.stdout+p.stderr,'output_sha256':hashlib.sha256((p.stdout+p.stderr).encode()).hexdigest(),'assurance':'elaborated' if p.returncode==0 else 'draft','limits':'Same evaluator; pinnedruntime,cacheddependencies; not clean independent replay.'}
(root/'receipts'/(source.stem+'.json')).write_text(json.dumps(r,indent=2));(root/'receipts'/(source.stem+'.'+str(time.time_ns())+'.json')).write_text(json.dumps(r,indent=2));print(p.stdout+p.stderr);print('EXIT',p.returncode,'SECONDS',r['elapsed_seconds']);sys.exit(p.returncode)
