# AHS27 and Local51 formalization status

Observed 2026-10-23. This records bounded compilation and actual-root transitive axiom checks, not final expert review. The runtime is pinned Lean 4.26.0 with the existing dependency cache.

| Module | Observed evidence |
|---|---|
| `AHS27Data` | exit=0; current source hash matches receipt; compiled object exists; its retained roots pass the isolation audit |
| `AHS27Trace` | exit=0; current source hash matches receipt; compiled object exists; its retained root passes the isolation audit |
| `AHS27Transport` | exit=0; current source hash matches receipt; compiled object exists; its retained roots pass the isolation audit |
| `AHS27Construction` | exit=0; current source hash matches receipt; compiled object exists; its retained roots pass the isolation audit |
| `AHS27Isolation` | exit=0, 32.12 seconds; current source hash matches receipt; compiled object exists; both isolation theorem roots pass the isolation audit |
| `AHS27IsolationAudit` | exit=0, 30.63 seconds; all 16 named actual theorem roots pass the explicit allowlist; **axiom-audited** |
| `Local51` | exit=0, 2.04 seconds; `FrontierLocal51.local_weight_le_51` passes the explicit allowlist; **axiom-audited** arithmetic implication |
| `AHS27SunflowerFree` | Pending: no successful completion receipt and no compiled object; not retried in this bounded recovery |
| `AHS27Audit` | Pending: full audit imports the unfinished sunflower-free module; no successful completion receipt and no compiled object |

The explicit allowlist is `propext`, `Classical.choice`, `Quot.sound`. Each of the 16 isolation audit roots has exactly this closure. The Local51 arithmetic theorem uses only `propext` and `Quot.sound`. The isolation audit deliberately omits `AHS_no_sunflower_triple` and `AHS_sunflowerFree`; its success does not discharge those two roots.

Observed logs and hash-bound receipts are in `receipts/AHS27IsolationAudit.bounded.{json,log}`, `receipts/AHS27IsolationAudit.axiom-audit.json`, `receipts/Local51.bounded.{json,log}`, and `receipts/Local51.axiom-audit.json`. The earlier isolation assembly receipt is `receipts/AHS27Isolation.json`. Source hashes were checked before writing this status; successful modules were not rebuilt.

## Remaining obligations

1. Finish the separate AHS27 sunflower-free proof within an authorized bounded approach; it remains pending.
2. After that succeeds, run the full 18-root `AHS27Audit` and inspect its actual output.
3. Formalize the geometry-to-arithmetic bridge for Local51 if an end-to-end geometric Lean theorem is required. Its numerical and structural hypotheses are currently explicit premises; the source check at `../highdegree/local51-geometry-check.md` is ordinary mathematics, not Lean evidence.

Resource constraint: at most one Lean process, 512 MiB Lean memory limit, one worker, and a 120-second timeout per invocation. No claim of clean kernel replay, independent reproduction, or mathematical frontier breakthrough follows from these bounded checks.
