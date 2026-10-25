"""Prepare common final-audit inputs only after ten actual committed rounds.

This is an input freezer, not an auditor, vote generator or publication gate.
"""
import argparse,hashlib,json,shutil,sys
from pathlib import Path
sys.path.insert(0,'/home/user/.codex/skills/superresearch-x2/scripts')
from native_research import NativeRunStore

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--attempt',type=int,default=1)
    args=ap.parse_args()
    if args.attempt<1:raise ValueError('Positive actual audit attempt required')
    b=Path(__file__).resolve().parent;bundle=NativeRunStore(b/'run').bundle()
    if len(bundle['rounds'])<10:raise ValueError('Ten actual complete rounds required')
    last=bundle['rounds'][-1];s=last['snapshot'];raw=(b/'manuscript.md').read_bytes()
    if s['phase'] not in ('same-version-acceptance','same-version-review'):raise ValueError('Same-version round required')
    if hashlib.sha256(raw).hexdigest()!=s['manuscript_sha256']:raise ValueError('Final manuscript changed')
    d=b/'public'/f'final{args.attempt:02d}';d.mkdir(exist_ok=False)
    for name in ('manuscript.md','contract.json','roster.json'):shutil.copyfile(b/name,d/name)
    for name,obj in [('complete-review-history.json',bundle),('snapshot.json',s)]:
        (d/name).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
    pins={key:s[key] for key in ('manuscript_sha256','evidence_sha256','verification_sha256')}
    pins['round_sha256']=last['round_sha256']
    (d/'bindings.json').write_text(json.dumps(pins,indent=2)+'\n')
    incoming=b/'incoming'/f'final{args.attempt:02d}';incoming.mkdir(exist_ok=False)
    (d/'assignment.md').write_text(f'''# Separate actual final audit, attempt {args.attempt}

Use your existing Chief, Alpha or Beta context and exact roster identity. This is a new actual audit after {len(bundle['rounds'])} committed rounds, not reuse of your last vote. Read the exact manuscript and complete committed history here, the snapshot evidence and verification, and the bound author-response history. Do not read the other auditors' current incoming files or pending journal.

Exact bindings are in bindings.json: {json.dumps(pins)}.

Assess validity, claim limits, contrary evidence, methods, reproducibility, ethics and unresolved objections. Confirm substantive repair of every earlier required change and major finding, not merely a numeric count. Do not infer certainty from prior agreement. Retain ordinary computer-assisted versus full Lean, shared-builder, imported H27, bounded-priority, same-provider-review and no-human-certification limits. Identify any decisive objection. At least three concrete, scoped substantive checks are required. Ask for central scheduling before a heavy job.

Return an actual JSON object with agent_id, role, context_id, manuscript_sha256, round_sha256, evidence_sha256, verification_sha256, summary, evidence_ids, decision, required_revisions, findings, revisions, checks, scope_assessments, issue_dispositions. Use the ordinary review protocol's field schemas; omit round and snapshot_sha256. scope_assessments has nonempty strings for validity, claim_limits, contrary_evidence, methods, reproducibility, ethics, unresolved_objections. issue_dispositions explicitly resolves any still-outstanding original issue by its exact ID, with status, reason and manuscript_locator; otherwise use an empty object and explain the actual history check. Acceptance is your decision, never required by this assignment. Accept only if no necessary revision or open major/critical objection remains.

Save your exact authored JSON to {incoming}/YOUR_ROLE.json and return the same JSON. The parent records actual responses without changing them. No manuscript edits, publication or external effects are authorized by this assignment.
''')
    print(json.dumps({'directory':str(d),'rounds':len(bundle['rounds']),**pins}))

if __name__=='__main__':main()
