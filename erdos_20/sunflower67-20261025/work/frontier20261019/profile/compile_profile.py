import sys,os,pathlib,json,subprocess,time,hashlib,fcntl
root=pathlib.Path(__file__).resolve().parent
base=root.parent
cfg=json.loads((base/'runtime.json').read_text())
old='/home/user/Documents/Codex/2026-09-22/you-ve-been-interrupted-unexpectedly-please/work/erdos20-v13/lean/.lake/build/lib/lean'
env=dict(os.environ)
env['LEAN_PATH']=':'.join([str(root),old,str(base/'build'),*cfg['package_paths']])
source=root/sys.argv[1]
target=source.with_suffix('.olean')
cmd=[cfg['lean'],'-o',str(target),str(source)]
with (base/'lean.lock').open('a') as lock:
    fcntl.flock(lock,fcntl.LOCK_EX)
    t=time.monotonic()
    r=subprocess.run(cmd,cwd=root,env=env,capture_output=True,text=True,timeout=300)
record={'source':str(source),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'command':cmd,'exit_code':r.returncode,'seconds':time.monotonic()-t,'output':r.stdout+r.stderr,
        'assurance':'elaborated' if r.returncode==0 else 'draft',
        'limitation':'uses hash-matched retained project objects and pinned dependency cache'}
source.with_suffix('.receipt.json').write_text(json.dumps(record,indent=2))
print(record['output']);print('EXIT',r.returncode,'SECONDS',record['seconds'])
sys.exit(r.returncode)
