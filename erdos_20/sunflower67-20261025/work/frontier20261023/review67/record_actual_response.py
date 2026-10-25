"""Wrap an already returned specialist-authored JSON artifact, without editing it.

Run only after observing the corresponding agent's real final response. The
local reference records that occurrence; it is not a vendor call ID/signature.
This script cannot create a scientific response or decide its validity.
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
    ap.add_argument('round',type=int)
    ap.add_argument('role')
    args=ap.parse_args()
    base=Path(__file__).resolve().parent
    roster=json.loads((base/'roster.json').read_text())
    agent=next(r for r in roster if r['role']==args.role)
    source=base/'incoming'/f'round{args.round:02d}'/(args.role+'.json')
    response=source.read_text()
    content=parse_json(response)
    if (content.get('agent_id')!=agent['agent_id'] or
        content.get('context_id')!=agent['context_id'] or
        content.get('role')!=args.role or content.get('round')!=args.round):
        raise ValueError('Actual response has wrong identity/round; request author correction')
    record=seal_record(content,dict(
        tool='collaboration.followup_task; specialist-authored public JSON artifact and observed final response',
        call_id=f'local-log:{agent["agent_id"]}:round-{args.round}:final-json:{source}',
        context_id=agent['context_id'],
        recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        synthetic=False,public_response=response,
        response_sha256=bytes_digest(response.encode('utf-8'))))
    destination=base/'records'/f'round{args.round:02d}'/(args.role+'.json')
    destination.parent.mkdir(parents=True,exist_ok=True)
    if destination.exists():
        raise FileExistsError(destination)
    # Native validation precedes writing the wrapper copy. The source is never changed.
    result=NativeRunStore(base/'run').record_submission(record)
    destination.write_text(json.dumps(record,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps(dict(role=args.role,**result)))


if __name__=='__main__':
    main()
