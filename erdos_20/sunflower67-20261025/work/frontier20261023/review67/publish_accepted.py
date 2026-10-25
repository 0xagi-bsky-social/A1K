"""Publish only the exact manuscript accepted by the real native review record."""
import argparse,json,sys
from pathlib import Path
sys.path.insert(0,'/home/user/.codex/skills/superresearch-x2/scripts')
from native_research import NativeRunStore, validate_review_bundle
from native_publication import publish_local
from render_report import renderer

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('bundle_name')
    args=ap.parse_args()
    base=Path(__file__).resolve().parent
    bundle=NativeRunStore(base/'run').bundle()
    manuscript=(base/'manuscript.md').read_bytes()
    validation=validate_review_bundle(bundle,manuscript)
    if validation.get('publication_eligible') is not True:
        raise ValueError('Actual final review is incomplete/ineligible: '+json.dumps(validation))
    root=base/'publication';root.mkdir(exist_ok=True)
    audit=base/'publication-audits'/args.bundle_name
    # Validate the leaf name before using it as a path; native publisher repeats it.
    import re
    if re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9._-]{2,95}',args.bundle_name) is None:
        raise ValueError('Invalid bundle leaf name')
    audit.mkdir(parents=True,exist_ok=False)
    for name,obj in [('review-bundle.json',bundle),('review-validation.json',validation)]:
        with (audit/name).open('x') as f:json.dump(obj,f,indent=2,ensure_ascii=False);f.write('\n')
    receipt=publish_local(bundle,manuscript,root,args.bundle_name,renderer=renderer)
    with (audit/'actual-publication-result.json').open('x') as f:
        json.dump(receipt,f,indent=2,ensure_ascii=False);f.write('\n')
    print(json.dumps({'status':receipt.get('status'),'bundle':str(root/args.bundle_name),
                      'review_count':validation['submission_count'],'final_round':validation['final_round']}))

if __name__=='__main__': main()
