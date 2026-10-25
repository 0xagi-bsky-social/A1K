"""Rebuild all packaged Lean sources, using caller-provisioned external package caches."""
from pathlib import Path
import argparse,json,hashlib,subprocess,os,time
p=argparse.ArgumentParser();p.add_argument('--lean',required=True);p.add_argument('--timeout',type=int,default=120);args=p.parse_args()
r=Path(__file__).resolve().parent;rows=json.loads((r/'source-manifest.json').read_text())
env=dict(os.environ);env['LEAN_PATH']=str(r/'build')+':'+env.get('LEAN_PATH','')
(r/'logs').mkdir(exist_ok=True)
for row in rows:
 src=r/row['path'];assert hashlib.sha256(src.read_bytes()).hexdigest()==row['sha256'],row['module']
 rel=Path(*row['module'].split('.')).with_suffix('.lean');out=(r/'build'/rel).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 cmd=[args.lean,'--threads=1','--memory=1024','-o',str(out),str(rel)];start=time.monotonic()
 try:
  q=subprocess.run(cmd,cwd=r/'source',env=env,capture_output=True,text=True,timeout=args.timeout);code,text=q.returncode,q.stdout+q.stderr
 except subprocess.TimeoutExpired as e:code,text=124,str(e.stdout or '')+str(e.stderr or '')
 receipt={'module':row['module'],'source_sha256':row['sha256'],'command':cmd,'exit_code':code,'seconds':time.monotonic()-start,'output':text}
 (r/'logs'/(row['module']+'.json')).write_text(json.dumps(receipt,indent=2)+'\n');print(row['module'],code,flush=True)
 if code:raise SystemExit(code)
print('All packaged sources rebuilt. Inspect audit outputs for the exact root checks.')
