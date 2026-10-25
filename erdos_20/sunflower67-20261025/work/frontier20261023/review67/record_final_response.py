"""Record an actually observed final auditor response; never create a judgment.

Run only after observing that reviewer's real final tool response. The native
store checks the ten completed rounds and exact final evidence/manuscript pins.
"""
import argparse
import datetime
import json
from pathlib import Path
import sys
sys.path.insert(0, '/home/user/.codex/skills/superresearch-x2/scripts')
from native_research import NativeRunStore, bytes_digest, parse_json, seal_record


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('role', choices=('chief','alpha','beta'))
    ap.add_argument('--attempt',type=int,default=1)
    args=ap.parse_args()
    if args.attempt<1: raise ValueError('positive actual attempt required')
    base=Path(__file__).resolve().parent
    roster=json.loads((base/'roster.json').read_text())
    agent=next(r for r in roster if r['role']==args.role)
    source=base/'incoming'/f'final{args.attempt:02d}'/(args.role+'.json')
    response=source.read_text()
    content=parse_json(response)
    for key in ('agent_id','context_id','role'):
        if content.get(key)!=agent[key]: raise ValueError('Identity mismatch: '+key)
    record=seal_record(content,dict(
        tool='collaboration.followup_task; specialist-authored final JSON artifact and observed final response',
        call_id=f'local-log:{agent["agent_id"]}:final-audit-{args.attempt}:{source}',
        context_id=agent['context_id'],
        recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        synthetic=False,public_response=response,
        response_sha256=bytes_digest(response.encode('utf-8'))))
    dest=base/'records'/f'final{args.attempt:02d}'/(args.role+'.json')
    dest.parent.mkdir(parents=True,exist_ok=True)
    if dest.exists(): raise FileExistsError(dest)
    result=NativeRunStore(base/'run').record_final_audit(record,(base/'manuscript.md').read_bytes())
    with dest.open('x') as f:json.dump(record,f,indent=2,ensure_ascii=False);f.write('\n')
    print(json.dumps({'role':args.role,**result}))

if __name__=='__main__': main()
