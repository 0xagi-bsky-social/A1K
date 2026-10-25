# Bounded reproducibility entry point

This note accompanies the ordinary computer-assisted upper-67 proof. It is not a
whole-proof clean replay and does not replace the written family-to-model bridges,
external theorem imports, complete case-coverage checks, or the review record.

## One exact degree-17 leaf, with fresh output

The archive evaluator's original command line deliberately refuses to overwrite
its canonical replay receipt. `../replay_d17_leaf_fresh.py` calls that unchanged,
source-pinned evaluator and writes its literal result to a new caller-owned path.
It reconstructs the necessary model with the same producer's `build()` function,
then performs exact integer certificate arithmetic. It does not run the LP solver.
Shared model construction remains an implementation dependency.

From the workspace root, the following invocation actually completed on
24 October 2026 (existing output must not be reused):

```bash
timeout 45s env OPENBLAS_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 \
  /home/user/Documents/Codex/2026-08-18/mission-autonomous-mathematical-reverse-engineering-formal/work/pyenv/bin/python \
  work/frontier20261023/review67/replay_d17_leaf_fresh.py \
  work/frontier20261023/highdegree/degree17_full/P9-Q8-E4_56-exterior-E4-stage1-v9-84c78c6484a5-phaseone.json \
  --output work/frontier20261023/review67/reproduction/Q8-E4_56-fresh.json
```

Observed result: `PASS`, `strict_exclusion: true`, 3.62555 seconds. The saved
receipt includes Python/NumPy/SciPy versions, input/source hashes and the exact
arithmetic. It is a single-leaf replay only. To repeat it, supply a **new** output
path. The wrapper refuses an existing destination; it does not rewrite archive
receipts. The source pin is
`10304e6fa2f3adfea9de387e82601ee6eef7f445b9460e35827d2e2eced634c8`.

## Other existing replay entry points

These are inspected command-line interfaces, not new executions performed by
this guide. Their earlier actual outputs and proof scopes are specified in the
named assembly notes and immutable review evidence. Always use fresh destinations.

| Scope | Script under `work/frontier20261023/highdegree/` | Required arguments and limits |
|---|---|---|
| Size-15 finite proof trees | `replay_r15_rho6_tree.py` | A literal `R15-rho6-*-search.json.gz` tree; `--output NEW_PATH --negative-controls`. Checks wrong target, omitted child and wrong source. |
| Degree-16 deletion covers | `replay_d16_i8_deletion_covers.py` | `--output NEW_PATH`. The script itself uses overwrite-capable `write_text`, so reserve a fresh caller-owned destination. |
| Degree-16 fibres | `replay_d16_fibres.py` | `--k 3` (separately 4, 5, 6), `--cover-receipt EXISTING_RECEIPT --output NEW_PATH --seconds 30`. Uses a C++ helper. `PARTIAL_PASS` from an intentionally restricted profile range is not complete coverage. |
| Cap-15 covers | `replay_low15_eight_seven_covers.py` | `--output NEW_PATH --seconds 10`. Do not omit the output: its default names an archived receipt. |
| Degree-17 Q8 literal stage coverage | `check_d17_stage_plan_v9.py` | `degree17_full/P9-Q8-complete-plan-v9.json --output NEW_PATH`. Thirty-second deadline; omit `--allow-partial` for complete-kind coverage. This verifies stored exact leaves and dependency/coverage conditions, not a fresh replay of every coefficient vector. |

The complete size-15 trees are `R15-rho6-two-triangles-search.json.gz`,
`R15-rho6-cycle5-search.json.gz` and `R15-rho6-triangle-path-search.json.gz`.
Their arbitrary-support normalization is a separate ordinary mathematical proof.
The degree-17 stage plans include absolute source paths and historical integrity
bindings; relocation requires a documented mapping, not silent substitution.

Do not invoke `recheck_R15_degree2_support.py` in place merely to obtain a fresh
receipt: that historical interface writes its archived destination directly.
The frozen original and its observed receipt remain available for inspection.

The exact external checks retain the SuperMath grade `certificate-diagnostic`.
No statement here upgrades them to a proved Lean evaluator, end-to-end Lean,
organizationally independent reproduction, or external human certification.
