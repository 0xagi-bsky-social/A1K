# Actual review campaign handoff to root

The root asked the coordinator to finish round 4 and then become idle so three reviewers can run concurrently. Do not restart or replace contexts. The process remains the same twelve actual isolated contexts across ten synchronous rounds, followed by actual Chief/Alpha/Beta audits.

Working directory: `/home/user/Documents/Codex/2026-10-09/https-github-com-openai-math-blob`.

Review directory: `work/frontier20261020/review`.

Read `RESUME.md`, `public-state.json`, and `python3 work/frontier20261020/review/manage.py status` for exact completion. Round 4 has COMMITTED: 48 actual submissions, 12 per round, all twelve roles participated in each of four phases. Round 4 hash is `7f908d55453a3e7ac67736b4df74bb014995e5bae1f732aab22d0351d1ed77ed`. All twelve round-4 decisions continue; outstanding_issues is empty. Round 5 has NOT been opened.

## Actual contexts

All were freshly created with `fork_turns="none"`. Each role's canonical ID, used for both `agent_id` and `context_id`, is:

```
/root/review80_coordinator/chief
/root/review80_coordinator/domain_expert
/root/review80_coordinator/literature_reviewer
/root/review80_coordinator/methodologist
/root/review80_coordinator/data_analyst
/root/review80_coordinator/logic_auditor
/root/review80_coordinator/citation_verifier
/root/review80_coordinator/academic_writer
/root/review80_coordinator/alpha
/root/review80_coordinator/beta
/root/review80_coordinator/copyeditor
/root/review80_coordinator/typesetter
```

Call `collaboration.followup_task` on these absolute IDs, not on newly spawned agents. They retain their own four-round history. When this coordinator is idle, root can run three concurrently. Do not trigger the coordinator while three reviewers are active.

## Frozen manuscript and evidence

Round 4 manuscript hash:
`686c89bd7044ce810ae26d59806f42f4e1d320a3f1243b3d72a3c785ded1318d`.

Round 4 snapshot:
`c2f8b6f772de5ed6e275d2fbce3557d05369213b9998c590634cd36b0b371329`.

The latest matching frozen preview is `evidence/preview-686c-v1`; prior preview IDs remain historical. `evidence.json` contains immutable versioned evidence records. All cited source and proof artifacts were copied into `evidence/`, including the 161-source portable closure and exact receipts. `verification.json` accurately records limited checks for all six required scopes. No claim of clean toolchain replay, independent authentication or exhaustive originality is supported.

Current public-state includes only committed peer findings. The immutable `public/round-NN` directories contain manuscript, snapshot, contract and roster. Agents must read those, not the mutable root manuscript or sibling pending responses.

## Next rounds

After round 4 is committed and any required edits are resolved/prepared:

```
python3 work/frontier20261020/review/manage.py open 5
```

This freezes current root manuscript and evidence/verification/public-state, opens the native store, prints exact hashes and updates RESUME. It does not dispatch reviewers.

Dispatch each role with an appropriately tailored version of:

> ROUND 5: frozen work/frontier20261020/review/public/round-05 is ready. Follow REVIEWER_PROTOCOL.md. Phase calculations, robustness and reproducibility. Perform one or two substantive role-specific checks, reusing unchanged verified evidence rather than repeating whole-artifact work. Read committed prior findings; explicitly close your own earlier required revisions if repaired. Write your actual response to responses/round-05/ROLE.json and return path, decision and concise findings. No current sibling pending outputs.

Every role must execute each phase. Focused analysis is sufficient; a copied prior judgment or schema/count-only acceptance is not.

Phases remaining:

5. calculations, robustness and reproducibility;
6. integrated manuscript;
7. skeptical review, all roles scrutinizing objections;
8. constructive review, all roles testing repairs;
9. revision and facts/citations/logic/method/data/text-reuse audit;
10. same-version final review and lock.

For each actual completion, preserve the specialist-authored JSON without modification:

```
python3 work/frontier20261020/review/manage.py record 5 ROLE
```

The helper reads that actual response, seals it with honest local tool/log provenance and actual canonical context ID, and calls NativeRunStore.record_submission. If the schema is wrong, ask that same reviewer to correct its response; do not write its scientific findings.

After all twelve are recorded:

```
python3 work/frontier20261020/review/manage.py commit
```

This refuses incomplete rounds, writes `committed/round-NN.json`, computes persistent issues, updates `public-state.json` and RESUME, and prints decisions/round hash. Do not share current-round findings until commit. Do not open the next round before commit. At the safe window apply any actual manuscript revisions, update coordinator_changes in public-state, append new evidence IDs when needed, and then open the next phase.

Root may proceed automatically between rounds when no concrete required edit remains. Reuse the same manuscript bytes; a new snapshot still binds the next phase and prior commitment. All 12 must participate even when the bytes are unchanged.

## Persistent issues and genuine repairs

Round 1 required explicit definitions of intersecting and maximum-cardinality f(4,3). Academic writer and Alpha explicitly closed both required revisions in round 2. Optional spacing and notation findings were also resolved.

Round 3 academic writer required narrowing the first sentence of Section 6: local structural proofs do not use the exploratory diagnostics, while Corollary 4 uses the external enumerative I(27). Root repaired this before round 4. The exact persistent required-revision key is:

`/root/review80_coordinator/academic_writer:round-3:required-revision-1`

The round 4 academic_writer response explicitly closed this required revision and associated finding. Copyeditor also explicitly closed its matching scope finding. The committed public-state has no outstanding issue.

Remaining known nonblocking issues before round 4 commit: HTML browser visual QA unavailable; source fidelity checked. PDF identifiers wrap awkwardly and Section 5 begins at a page end, but all six pages were actually inspected and no content loss was found. These are disclosed note/minor issues, not publication-blocking major defects. Main scientific limitations remain explicit external I27, no universal45 proof, no exhaustive novelty, no independent human certification.

## Separate final audits after round 10

Read `/home/user/.codex/skills/superresearch-x2/references/native-review.md` for exact final schema. Do not infer acceptance from round 10.

After at least ten complete rounds and a same-version final round, prepare one frozen public final package containing the exact final manuscript and complete committed review history, contract/roster/evidence/verification. Capture its hash as useful. All three must see the same package; withhold their current final responses from one another.

Example extraction (use Python, not shell interpolation of text):

```
import sys, json
from pathlib import Path
sys.path.insert(0, '/home/user/.codex/skills/superresearch-x2/scripts')
from native_research import NativeRunStore
R = Path('work/frontier20261020/review')
bundle = NativeRunStore(R/'run').bundle()
(R/'public'/'final-review-history.json').write_text(json.dumps(bundle, indent=2)+'\n')
```

Call the existing chief, alpha and beta contexts separately (three may run concurrently after coordinator is idle). Ask each to actually audit the final exact bytes and all ten rounds, assess unresolved objections and check assurance limits, and write `responses/final/ROLE.json`.

Final content uses common submission fields (`agent_id`, `role`, `context_id`, `manuscript_sha256`, `summary`, `evidence_ids`, `decision`, `required_revisions`, `findings`, `revisions`, `checks`) but replaces `round` and `snapshot_sha256` with:

* `round_sha256`: last committed round hash;
* `evidence_sha256`, `verification_sha256`: exact final-round snapshot values;
* `scope_assessments`: nonblank substantive assessments of validity, claim_limits, contrary_evidence, methods, reproducibility, ethics, unresolved_objections;
* `issue_dispositions`: explicit status/reason/manuscript_locator for any still-outstanding prior issue.

All three must actually accept with no required revision or open major/critical issue. An original reviewer may close its own earlier required revision in a later round using the full exact key; otherwise all final reviewers must substantively dispose of it. No issue disappears merely from omission.

For each actual final response:

```
python3 work/frontier20261020/review/manage.py final chief
python3 work/frontier20261020/review/manage.py final alpha
python3 work/frontier20261020/review/manage.py final beta
python3 work/frontier20261020/review/manage.py export
```

The last command writes `review-bundle.json` and `validation.json`. Both valid and publication_eligible must be true before root publication. The helper reads the exact root manuscript, so any changed bytes invalidate approval. The immutable bundle preserves all actual responses and local provenance; it cannot authenticate agents externally.

If any final reviewer rejects, retain the rejection. Make substantive repairs, run a complete further same-version round, and obtain new actual audits from all three. Never rewrite a rejection into acceptance. Root owns publication and final delivery; coordinator has not published anything.
