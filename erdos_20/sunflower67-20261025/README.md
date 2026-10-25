# Upper 67: proof sources and evidence

This collection accompanies the 25 October 2026 paper [*An upper bound for four-uniform three-sunflower-free families*](work/frontier20261023/review67/publication/sunflower67-20261025/report.md). The [HTML](work/frontier20261023/review67/publication/sunflower67-20261025/report.html) and [PDF](work/frontier20261023/review67/publication/sunflower67-20261025/report.pdf) preserve the same publication.

The paper gives an ordinary computer-assisted proof of **54 ≤ M(4, 3) ≤ 67**. Here M is the maximum size of a finite simple four-uniform family with no three-sunflower, including an empty core. The lower bound 54 is unchanged. The argument uses the published intersecting bound H27, Jin's graph theorem, and specified prior structural results; the general Erdős–Rado sunflower conjecture remains outside its scope.

The transfer adds **389 Lean source instances**, covering **72 distinct new source contents** relative to the retained v13 archive, and **4,522 source and evidence files** in total. The [global Lean source index](../indexes/lean-source-files.csv), [artifact inventory](../indexes/sunflower67-artifacts.csv), [external-reference index](../indexes/sunflower67-external-references.csv), and [omission index](../indexes/sunflower67-omitted-artifacts.csv) record exact paths, roles, sizes, hashes, and dispositions. Repeated source instances preserve different project layouts; they are not counted as distinct new proofs.

## Follow the proof

Begin with the [global ordinary theorem](work/frontier20261023/highdegree/GLOBAL67-ordinary-theorem.md) and [acyclic dependency roadmap](work/frontier20261023/highdegree/GLOBAL67-dependency-roadmap.md). They identify the imports, mathematical bridges, active certificates, and order in which the degree bounds become available.

| Branch | Main assembly |
| --- | --- |
| Degree 20 | [D20-proof-check.md](work/frontier20261023/highdegree/D20-proof-check.md) |
| Degree 19 | [D19-complete-argument.md](work/frontier20261023/highdegree/D19-complete-argument.md) |
| Degree 18 | [D18-complete-argument.md](work/frontier20261023/highdegree/D18-complete-argument.md) |
| Degree 17 | [D17-complete-argument.md](work/frontier20261023/highdegree/D17-complete-argument.md) |
| Degree 16 | [D16-complete-argument.md](work/frontier20261023/highdegree/D16-complete-argument.md) |
| Maximum degree at most 15 | [LOW15-complete-argument.md](work/frontier20261023/highdegree/LOW15-complete-argument.md) and [direct Jin add-on](work/frontier20261023/highdegree/LOW15-direct-Jin-A3-addon.md) |

The active degree 19, 18 and 17 chains contain 43, 169 and 329 finite leaves. These are branch incidences, with some evidence reused. The degree 17 count is 12 + 131 + 92 + 94. Numerical optimization proposes certificate multipliers; the exact replayers check the full integer expression and a strict contradiction. Separate literal checks reconstruct orbit coverage and ancestry. Those checks complement the written family-to-model implications.

The new fifteen-triple theorem says that every simple three-uniform family with no three-sunflower has, at size fifteen, a member disjoint from at least seven others. Its arbitrary-support reduction, degree-two analysis, finite proof trees and independently written replayers are identified in the [paper's companion map](work/frontier20261023/review67/publication/sunflower67-20261025/report.md#companion-proof-and-evidence-map).

## Read the formal evidence at its stated scope

The [42 historical root entries](../indexes/sunflower67-formal-roots.csv) and [72 new distinct Lean contents](../indexes/sunflower67-new-lean-contents.csv) provide direct source and receipt locators. Counts of source contents and audit entries are not counts of new global theorems.

The latest [formal directory](work/frontier20261023/formal/) contains terminal and trace-pool lemmas, construction-isolation results, and five size-fifteen arithmetic interfaces. Its status notes and hash-bound receipts state which roots compiled and passed their transitive axiom audits. The allowlist is `propext`, `Classical.choice`, and `Quot.sound`; the five new arithmetic roots use only `propext` and `Quot.sound`.

[AHS27 status](work/frontier20261023/formal/STATUS.md) records the unfinished `AHS27SunflowerFree` module and full `AHS27Audit`. A successful isolation audit does not supply the two omitted sunflower-free roots. Draft and negative-control files remain classified as such in the source inventory.

The [20 October formal source bundle](work/frontier20261020/release-formal/README.md) is an intermediate development: its main formal root proves **I(27) implies G(80)**. It records a 161-module closure, 63 fresh compilations, 98 source-matched prior successful rebuilds, and renewed root axiom audits. It also proves the unconditional two-noncooccurring-degree-twenty-star bound of 80. Earlier finite-support reductions and their evidence are retained in the 19 October material. These intermediate results are distinct from the latest ordinary upper-67 proof. The portable intermediate bundle uses its custom `rebuild.py`, explicit dependency paths and pinned manifest; it is not a standalone Lake project. The latest historical compilation wrappers also require a documented relocation of their original build and runtime paths.

**The full upper-67 theorem is not an end-to-end Lean closure.** Neither the external H27 ledger nor the complete LP models, proof-tree predicates and geometric bridges have all been assembled in Lean. Historical receipts describe the original research runs under pinned Lean 4.26.0 dependencies and an existing cache. This repository transfer does not claim a new full build, clean-toolchain replay, independent-host reproduction, or independent human certification.

## Check and reproduce

From the repository root, run:

```bash
python3 erdos_20/tools/verify_inventory.py
```

The inventories bind the shipped source bytes and external-reference commitments. The [static dependency summary](dependency-binding-summary.json) records 29,319 path/hash checks across 1,061 reachable JSON files, with no mismatch or unresolved binding. This is a byte-binding audit, not a fresh reconstruction of the models or a mathematical proof audit. A hash check establishes consistency with an unsigned inventory; it does not prove a theorem or authenticate an external historical computation.

The original [bounded reproduction guide](work/frontier20261023/review67/reproduction/README.md) gives the inspected command interfaces and their limits. Original scripts and receipts retain their bytes, source pins and host paths. Research paths beginning `work/` resolve from this collection directory. Absolute paths name the original research host and require an explicit relocation map. Do not rewrite committed canonical receipts when repeating a check; use a fresh output under `.local/`.

For example, the cap-15 cover reconstruction uses Python's standard library and an explicit fresh destination:

```bash
cd erdos_20/sunflower67-20261025
mkdir -p .local
PYTHONDONTWRITEBYTECODE=1 python3 \
  work/frontier20261023/highdegree/replay_low15_eight_seven_covers.py \
  --output .local/cap15-covers.json --seconds 10
```

The [transfer checks](transfer-checks/summary.json) record fresh successful runs of the cap-15 cover reconstruction (2,541 cases), the degree-16 cover reconstruction (5,576 cases), and all three size-fifteen proof trees (12,221 nodes and 384,857 colour-pair checks). The three tree replays also rejected the tested wrong-target, omitted-child and wrong-source controls. These are bounded external checks, with the separate ordinary support reductions still required.

The degree-16 cover and fibre checks and the size-fifteen proof-tree replayer have separate interfaces. The fibre check needs a C++ compiler. LP coefficient replay additionally requires the pinned producer's numerical Python dependencies; it reconstructs a model through shared producer code and does not become an independent model implementation merely because the arithmetic is exact.

Some prior-art sources are linked instead of redistributed because their repository has no project-wide redistribution license. Before running a checker that imports them, obtain the exact pinned checkout at `work/frontier20261020/prior-art68/repository` and verify it against the external-reference index. Their expected commit is `90c03c79bcf44eb8f61dff1b86091b822cc4cd3c`. The archive does not silently substitute a current upstream revision.

## Provenance and historical records

The source archive preserves relative paths so plans, receipts, status notes and written bridges remain inspectable together. Completed assemblies name the later evidence that supersedes pending statements in earlier preparation notes. Historical or failed calculations are evidence of the development process, not additional accepted proof leaves.

The publication's review records preserve the actual specialist contexts, rounds, revisions, dissent and final manuscript audits. Separate agent contexts do not establish organizational independence or human certification. The literature search has the bounded scope and access gaps stated in the paper; it does not certify exhaustive global originality.

The root [license and third-party notice](../../THIRD_PARTY_NOTICES.md) also apply here. Original source headers and AI-assistance attributions are preserved. Upstream references retain their authors' rights and are not relicensed by A1K.
