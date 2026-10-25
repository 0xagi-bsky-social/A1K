import json,os,subprocess,sys,time,hashlib
from pathlib import Path
p=Path(__file__).resolve().parent
root=p.parents[2]
cfg=json.loads((root/'work/frontier20261019/runtime.json').read_text())
name=sys.argv[1];source=p/(name+'.lean');obj=p/'build'/(name+'.olean')
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(p/'build'),str(root/'work/frontier20261020/closure-rebuild/build'),*cfg['package_paths']])
command=[cfg['lean'],'-j1','-M512','-o',str(obj),str(source)]
before=source.read_bytes();started=time.monotonic()
try:
    proc=subprocess.run(command,cwd=root,env=env,text=True,capture_output=True,timeout=120)
    code=proc.returncode;output=proc.stdout+proc.stderr;status='completed'
except subprocess.TimeoutExpired as err:
    code=None;status='timeout';output='TIMEOUT at120seconds\n'
    for part in (err.stdout,err.stderr):
        if part:output+=part.decode() if isinstance(part,bytes) else part
receipt={'module':name,'exit_code':code,'status':status,'elapsed_seconds':time.monotonic()-started,
         'command':command,'source_sha256':hashlib.sha256(before).hexdigest(),
         'source_stable':before==source.read_bytes(),'lean_path':env['LEAN_PATH'],
         'object_sha256':hashlib.sha256(obj.read_bytes()).hexdigest() if code==0 and obj.exists() else None,
         'output_sha256':hashlib.sha256(output.encode()).hexdigest(),
         'assurance':'elaborated' if code==0 else 'incomplete',
         'limits':'pinned existing dependency cache; not clean independent reproduction'}
(p/'receipts'/(name+'.bounded.json')).write_text(json.dumps(receipt,indent=2)+'\n')
(p/'receipts'/(name+'.bounded.log')).write_text(output)
print(output[:6000]);print(json.dumps({k:receipt[k] for k in ('module','exit_code','status','elapsed_seconds','assurance')}))
sys.exit(code if code is not None else 124)
