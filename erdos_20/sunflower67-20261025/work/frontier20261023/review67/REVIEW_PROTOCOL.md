# Actual specialist review protocol

Read the round's immutable manuscript.md, snapshot.json, contract.json and roster.json. Confirm the supplied manuscript and canonical snapshot hashes. Apply your exact roster role and this round's public phase. You may follow named evidence files and their underlying proof/source/receipt pointers. You may browse relevant primary sources, preserving access limits. Do not read the run journal, incoming directory except your own response file, or any other specialist's current-round output. Previous committed rounds will be supplied as public history in later snapshots.

Perform substantive scientific review appropriate to this round, with actual file/source inspection and concrete locators. Do not infer correctness from the frontier gate, author confidence or the existence of PASS strings. Distinguish accepted mathematical theorem imports from locally re-proved results; distinguish an ordinary computer-assisted proof from Lean assurance. A decisive counterexample or uncovered premise must be reported. Early rounds need not certify every finite leaf. At least three concrete check records are requested per submission, scoped honestly to what you inspected. Do not run a heavy solver, full replay or compiler in parallel: request central scheduling from the parent first. Ordinary read-only and cheap bounded standard-library checks are allowed.

Return one actual JSON object in your final answer, with no Markdown fences. Also save those exact public JSON bytes to your assigned incoming file. Do not edit the manuscript or other review files. The parent records and hashes your actual result; it will not manufacture a decision. Use the following schema (all fields required):

{
 "agent_id":"your actual roster agent_id",
 "role":"your exact roster role",
 "context_id":"your actual roster context_id",
 "round":1,
 "snapshot_sha256":"supplied canonical snapshot hash",
 "manuscript_sha256":"supplied exact manuscript hash",
 "summary":"your conclusion-level assessment",
 "evidence_ids":["only IDs from this snapshot"],
 "decision":"continue or revise or reject or accept",
 "required_revisions":["actual requested revisions; empty if none"],
 "findings":[{"id":"stable local finding ID","statement":"specific issue","severity":"note/minor/major/critical","status":"open/resolved/claim-qualified/not-applicable","disposition":"reason or action","evidence_ids":[]}],
 "revisions":[{"finding_id":"exact earlier finding or required-revision ID","action":"actual action assessed","result":"assessment","status":"resolved/claim-qualified/not-applicable"}],
 "checks":[{"scope":"precise scope","method":"actual inspection or check","observation":"actual result with file/section/source locator","result":"supported/contradicted/inconclusive/not_applicable","evidence_ids":[]}]
}

Allowed decision, severity, status and check-result strings are literal alternatives, not slash-separated values. An acceptance cannot retain required revisions or open major/critical findings. A necessary manuscript revision should not be silently waived. In later rounds, close earlier required revisions explicitly using agent_id:round-N:required-revision-I (I starts at1) and give a reason, or preserve the objection. No objection disappears merely because a later findings list is empty.

This is autonomous same-environment agent review. Distinct contexts are not independent human or organizational certification. No publication occurs before ten complete twelve-role rounds and separate same-manuscript Chief/Alpha/Beta final audits.
