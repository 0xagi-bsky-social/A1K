"""Freeze and rebuild the new proof closure; reuse only source-matched 20261019 rebuilds."""
from pathlib import Path
import re, json, hashlib, os, subprocess, time, sys, shutil
R=Path(__file__).resolve().parent
W=R.parent
C=W.parent
OLD=W/'frontier20261019/lean'
BASE=C/'outputs/frontier20261019/formal/source-rebuild-receipt'
OUT=R/'closure-rebuild'
CFG=json.loads((W/'frontier20261019/runtime.json').read_text())
new={p.stem:p for d in ('formal','theory','compute') for p in (R/d).glob('*.lean')}
def source(m):
 return new.get(m) or OLD.joinpath(*m.split('.')).with_suffix('.lean')
def digest(b): return hashlib.sha256(b).hexdigest()
def dump(p,v): p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(v,indent=2)+'\n')
order=[];seen=set()
def visit(m):
 if m in seen:return
 p=source(m)
 if not p.exists():return
 seen.add(m)
 for x in re.findall(r'^import\s+([\w.]+)',p.read_text(),re.M):visit(x)
 order.append(m)
for m in sys.argv[1:]:visit(m)
manifest=[];reused=[];todo=[]
for m in order:
 p=source(m);b=p.read_bytes();h=digest(b)
 row={'module':m,'source':str(p),'source_sha256':h}
 rec=BASE/'base-logs'/f'{m}.json'
 reuse=False
 if m.startswith('SunflowerLean.') and rec.exists():
  rr=json.loads(rec.read_text())
  reuse=rr['exit_code']==0 and rr['source_stable'] and rr['source_sha256']==h
 if reuse:reused.append(m)
 else:
  cp=OUT/'source'/Path(*m.split('.')).with_suffix('.lean');cp.parent.mkdir(parents=True,exist_ok=True);cp.write_bytes(b);todo.append(m)
 row['mode']='source-matched previous rebuild' if reuse else 'fresh rebuild';manifest.append(row)
if (OUT/'summary.json').exists():
 shutil.copyfile(OUT/'summary.json',OUT/('summary-previous-'+str(time.time_ns())+'.json'))
for m in reused:
 rel=Path(*m.split('.')).with_suffix('.olean')
 target=OUT/'build'/rel;target.parent.mkdir(parents=True,exist_ok=True)
 shutil.copyfile(BASE/'base-build'/rel,target)
dump(OUT/'manifest.json',manifest)
env=dict(os.environ);env['LEAN_PATH']=':'.join(map(str,[OUT/'build',BASE/'base-build',*CFG['package_paths']]))
start=time.monotonic();records=[]
for m in todo:
 cp=Path(*m.split('.')).with_suffix('.lean');obj=(OUT/'build'/cp).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 cmd=[CFG['lean'],'--memory=1024','--threads=1','-o',str(obj),str(cp)]
 st=time.monotonic()
 try:
  p=subprocess.run(cmd,cwd=OUT/'source',env=env,text=True,capture_output=True,timeout=120)
  code,out=p.returncode,p.stdout+p.stderr
 except subprocess.TimeoutExpired as ex:
  code=124;out='RESOURCE LIMIT 120 seconds\n'+str(ex.stdout or '')+str(ex.stderr or '')
 rr={'module':m,'source_sha256':digest((OUT/'source'/cp).read_bytes()),'command':cmd,'exit_code':code,'seconds':time.monotonic()-st,'output':out}
 dump(OUT/'logs'/f'{m}.json',rr);dump(OUT/'logs'/f'{m}.{time.time_ns()}.json',rr);records.append(rr)
 print(m,code,round(rr['seconds'],2),flush=True)
 if code:
  print(out,flush=True)
  dump(OUT/'summary.json',{'status':'fail','failed':m,'completed':len(records),'reused':reused});sys.exit(code)
for row in manifest:
 if digest(Path(row['source']).read_bytes())!=row['source_sha256']:raise RuntimeError('Source changed during rebuild: '+row['module'])
dump(OUT/'summary.json',{'status':'pass','fresh_modules':todo,'source_matched_reused_modules':reused,'closure_module_count':len(order),'fresh_count':len(todo),'reused_count':len(reused),'seconds':time.monotonic()-start,'manifest_sha256':digest((OUT/'manifest.json').read_bytes()),'LEAN_PATH':env['LEAN_PATH'],'limitation':'Same evaluator; source-matched previous base rebuild and pinned Lean/mathlib package caches retained. Not a clean-kernel replay or independent reproduction.'})
