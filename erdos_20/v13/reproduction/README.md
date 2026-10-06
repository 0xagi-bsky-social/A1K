# Version 13 local reproduction harness

`replay_v13.py` is a standalone integrity/replay tool. It does not establish a
SuperResearch publication gate, independent reproduction, source authenticity,
or independent certification. The host capability assessment is separate.

The expected source-manifest and policy digests must be retained outside the
mutable files being checked. The version-13 development records provide unsigned
local commitments; they must not be described as an external authority signature.
Pin creation records observed bytes. It does not certify that a dependency cache
was built from its pinned source revision.

## Enforced checks

- A nonempty source manifest must cover exactly every protected `SunflowerLean`
  and `negative` Lean file plus the policy's mandatory build/audit metadata.
  Duplicate keys, malformed hashes, escaping paths and source symlinks fail.
- The policy binds the runner, full compiler binary/version, complete toolchain
  library tree (including standard-library objects and internal symlink targets),
  dynamic-library bytes and the exact nine locked Git revisions. Tracked source
  modifications, extra package directories, project namespace shadowing and
  conflicting dependency object names fail. Every dependency cache tree is hashed.
- Each new run uses a new directory and fresh project object tree. Local import
  order comes from this release's restricted one-line import syntax; unresolved
  local dependencies and cycles fail. No project cache from a previous run enters
  `LEAN_PATH`.
- Resume rechecks all pinned inputs and command options, the run/context identity,
  every process/start/enriched receipt, source identities, object and log hashes,
  and the complete attempted-work index. It preserves the run ID and charged
  failures. An orphaned started or finalized attempt fails closed pending explicit
  reconciliation; the runner does not invent a historical completion.
- Every compiler attempt has distinct immutable started/process records. Successful
  validation adds a separate immutable enrichment. Status and event writes use
  fsync and atomic operations. SIGINT/SIGTERM, timeout, failed launch and normal
  compiler failure have distinct outcomes. SIGKILL or host failure can leave a
  started-only record, which is retained and blocks automatic resume.
- Source bytes are checked immediately before and after compilation. Source and
  entire environment commitments are checked again before completion. This detects
  persistent drift; it is not protection from a privileged writer that changes and
  restores bytes between observations.
- A negative test passes only on ordinary Lean exit code 1 with exactly one JSON
  error at its registered file and source span matching the frozen full-message
  pattern. A crash, timeout, earlier helper error or unknown identifier fails.
- A policy can select the authoritative audit module, needed when separate
  diagnostic audit modules also exist. The selected output must cover the exact
  nonempty root inventory once, with only `propext`, `Classical.choice`, and
  `Quot.sound`. No partial replay receives a completion receipt.

## Resources and limits

Receipts record compiler elapsed time, user/system CPU time, Linux peak RSS,
warnings, explicit command options and source `set_option` directives. A Linux
subreaper kills and reaps ordinary process-group descendants on termination.
This does not confine deliberately escaping descendants; stronger hostile-process
isolation would require a host cgroup or service. The log ceiling is polled and
can overshoot between polls; actual log bytes remain hash-bound. Peak RSS is the
maximum observed child high-water mark, not aggregate concurrent RAM. Compiler
wall budgets count attempts, including failures; environment hashing and elapsed
time between separate resume invocations are outside that compiler budget.

## Validation artifacts

`test_replay_v13.py` uses disposable synthetic compilers to exercise state handling
and corruption rejection. These tests certify no mathematical statements.
The separate `smoke-project` integration uses the actual pinned Lean executable,
two small source modules, two environment-derived axiom audits and a designated
false arithmetic assertion; it checks actual checkpoint/resume behavior.
`negative` contains three report-specific new controls. Failed drafts and a
timeout in the transversal control are retained under `../evidence/negative-structured`;
only its final exact-target result counts.

The full version-13 project-source replay is recorded separately by the parent
workflow. Do not infer that this harness itself rebuilt all report sources merely
because its small integration and source-commitment checks pass.

## Commands

Run `python3 replay_v13.py replay --help` for the required arguments. Supply a
frozen `policy.json`, external expected policy/source-manifest hashes, explicit
Lean executable, exact packages directory and fresh runs directory. `--check-only`
checks source commitments without compiling. `--stop-after N` produces an explicit
checkpoint; `--resume RUN_ID` preserves its identity and revalidates all inputs.

`verify-release` checks a separately pinned `erdos20-release-commitment/1` record
whose `files` map binds relative artifact paths to hashes. The record should bind
report, source, archive, review and replay identities; its bytes are an unsigned
release commitment, not evidence of authenticated origin. Archive-byte identity
and source-tree identity are distinct, so repacking may change only the former.
