import json, os, subprocess, sys, time, hashlib
from pathlib import Path
root=Path(__file__).resolve().parents[3]
p=Path(__file__).resolve().parent
runtime=json.loads((root/'work/frontier20261019/runtime.json').read_text())
env=os.environ.copy()
env['LEAN_PATH']=':'.join([str(p/'build'),str(root/'work/frontier20261020/closure-rebuild/build'),*runtime['package_paths']])
module=sys.argv[1]
source=p/(module+'.lean')
start=time.time()
with (p/'receipts'/(module+'.log')).open('w') as log:
    proc=subprocess.Popen([runtime['lean'],'-o',str(p/'build'/(module+'.olean')),str(source)],env=env,cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    for line in proc.stdout:
        log.write(line); log.flush(); print(line,end='',flush=True)
    code=proc.wait()
receipt={'module':module,'exit_code':code,'elapsed_seconds':round(time.time()-start,3),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'lean':runtime['lean'],'lean_version':runtime['version'],'lean_path':env['LEAN_PATH']}
(p/'receipts'/(module+'.json')).write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
sys.exit(code)
