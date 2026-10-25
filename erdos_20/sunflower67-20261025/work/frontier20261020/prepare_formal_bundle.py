from pathlib import Path
import json,hashlib,shutil
R=Path(__file__).resolve().parent;C=R.parents[1]
P=R/'release-formal';P.mkdir(exist_ok=True)
manifest=json.loads((R/'closure-rebuild/manifest.json').read_text());rows=[]
for row in manifest:
 b=Path(row['source']).read_bytes();assert hashlib.sha256(b).hexdigest()==row['source_sha256']
 rel=Path(*row['module'].split('.')).with_suffix('.lean');p=P/'source'/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 rows.append({'module':row['module'],'path':'source/'+rel.as_posix(),'sha256':row['source_sha256'],'recorded_check':row['mode']})
(P/'source-manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
for f in ['summary.json','manifest.json']:shutil.copyfile(R/'closure-rebuild'/f,P/('rebuild-'+f))
for f in ['LICENSE','NOTICE','THIRD_PARTY_NOTICES.md','ATTRIBUTION.md','lake-manifest.json','lean-toolchain']:shutil.copyfile(C/'outputs/frontier20261019/formal'/f,P/f)
shutil.copyfile(R.parent/'frontier20261019/runtime.json',P/'observed-runtime.json')
(P/'audit-logs').mkdir(exist_ok=True)
for p in (R/'closure-rebuild/logs').glob('*Audit.json'):shutil.copyfile(p,P/'audit-logs'/p.name)
(P/'README.md').write_text('''# Rank-four eighty endpoint: source proof bundle

Main root: `FrontierFinalEighty.rank_four_upper_eighty_of_intersecting_twenty_seven`.
It proves **I(27) implies G(80)**. I(27) remains a local ordinary hypothesis.
The ordinary corollary G(80) uses the explicit external computer-assisted I(27)
theorem in arXiv:2609.06175v1; this package does not certify that enumeration.

Unconditional structural root:
`FrontierTwoHighEighty.independent_twenty_stars_card_le_eighty`.
Two distinct noncooccurring degree20 points in a finite4-uniform SF3 family
force total cardinality at most80. No ambient support bound or I27 is assumed.

Sources are listed in topological order in source-manifest.json, with exact hashes.
The recorded closure has161modules:63freshlycompiled and98source-matched prior
successful rebuilds. Root axiom audits were rerun in the rebuilt closure. Only
propext, Classical.choice, Quot.sound occur. Grade: axiom-audited. No independent
human certification or clean-toolchain replay is claimed.

To rebuild all161sources, provision Lean4.26.0 and the exact package versions in
lake-manifest.json (mathlib2df2f0150c275ad53cb3c90f7c98ec15a56a1a67). Set LEAN_PATH
only to those external package olean roots and run:

    python3 rebuild.py --lean /absolute/path/to/lean

This command prepends its own new build directory, checks source hashes, then
compiles every module in topological order. It retains commands and outputs.
This is a reproducibility recipe, not an assertion it ran on another machine.
The observed-runtime.json records this task's actual installed paths.

See audit-logs for actual successful audits and rebuild-summary.json for the
recorded source-closure check. Exploratory cap45, failed bitmask proof attempts,
and UNKNOWN SAT runs are outside this accepted source bundle.

Inherited A1K source provenance:0e9aee578a7bb3dbc665630c759297514f88a81d.
Retained attribution/license files describe inherited upstream code; current
research sources are in the unprefixed modules under source/.
''')
print(str(P),len(rows))
