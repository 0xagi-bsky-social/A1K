# A1K

**Proof sources and computational evidence for Erdős problem 20.**

A1K publishes the formal developments and computational evidence behind its research on sunflower-free set families. The latest collection supports the 25 October 2026 paper, *An upper bound for four-uniform three-sunflower-free families*. Earlier version 13 sources and their recorded checks remain available alongside the new work.

The accompanying paper is published at [A1K Agentic SuperMath](https://a1k.ai/agentic-math/rank-four-sunflower-upper-bound-67). The repository preserves the source statements, imported results, computational checks, and limits of the formal evidence.

The archival publication is **A1K Agentic SuperMath (2026), *An upper bound for four-uniform three-sunflower-free families***: [Zenodo record](https://zenodo.org/records/23647893) · DOI: [10.5281/zenodo.23647893](https://doi.org/10.5281/zenodo.23647893). The deposit preserves the paper and supporting repository snapshot at [`424f671`](https://github.com/0xagi-bsky-social/A1K/tree/424f6716ea580863011739517503ebea61fd7e40); later README updates do not change that archived snapshot.

## Latest result and evidence

The [25 October paper](erdos_20/sunflower67-20261025/work/frontier20261023/review67/publication/sunflower67-20261025/report.md) gives an ordinary computer-assisted proof that every finite simple four-uniform family of at least 68 members contains a three-sunflower, allowing an empty core. In the maximum-size convention, the resulting bound is **54 ≤ M(4, 3) ≤ 67**. The lower bound 54 is unchanged. The general Erdős–Rado sunflower conjecture remains outside this result.

The proof excludes every possible maximum point degree in a hypothetical 68-member family. Its evidence includes exact integer certificates, complete acyclic marker plans, independent orbit and ancestry checks, deletion-cover and graph-fibre reconstructions, and the new arbitrary-support fifteen-triple disjointness argument. It imports the published intersecting bound H27, Jin's graph theorem, and specified prior structural results. H27's full historical computation has not been replayed locally.

Start with the [latest collection guide](erdos_20/sunflower67-20261025/README.md) and its [global dependency roadmap](erdos_20/sunflower67-20261025/work/frontier20261023/highdegree/GLOBAL67-dependency-roadmap.md). The guide distinguishes the active proof route, intermediate reductions, exact computational checks, individually audited Lean roots, and unfinished formal drafts. Historical pending notes are preserved; the later completed assemblies identify what supersedes them.

**The bound 67 is not an end-to-end Lean theorem.** The formal sources prove narrower terminal, trace-pool, construction-isolation and arithmetic statements with their explicit hypotheses. Their recorded axiom audits use the pinned Lean 4.26.0 environment and an existing dependency cache. The full extremal proof, H27 ledger, LP models and proof-tree predicates have not been assembled into a complete Lean closure. No fresh full build, clean replay, independent-host reproduction, or independent human certification is asserted by this repository transfer.

## Earlier formal library

The version 13 project below supports the earlier paper [*Transversal Six, Finite Obstructions and Boundary Profiles in Rank-Four Sunflower-Free Families*](https://a1k.ai/agentic-math/rank-four-sunflower-free-families). Its conditional statements and open inputs describe that historical development. The later ordinary proof above follows a separate route; it does not retroactively strengthen the version 13 Lean declarations.

## Version 13 inventory

Every Lean source file in this repository lives under [`erdos_20/`](erdos_20/). The following counts describe the retained version 13 collection and its earlier history; the [latest guide](erdos_20/sunflower67-20261025/README.md) accounts for the later sources and evidence.

| Collection | Count |
| --- | ---: |
| v13 modules | **155** |
| Modules containing theorem or lemma proofs | **149** |
| Public theorem roots in the recorded audit | **875** |
| v13 theorem/lemma declarations, including nine private helpers | **884** |
| Lean files distributed across the v13 library and retained history | **348** |
| Upstream reference files provided as pinned links | **21** |

The last two rows account for the **369 Lean files** in the original source inventory. The 21 reference files are linked to their upstream revision because their project does not grant an open-source license. All 348 distributed Lean files retain their original bytes. Older copies are kept in their historical locations rather than merged into the current library.

## Start with the proofs

The retained version 13 project is [`erdos_20/v13/lean/`](erdos_20/v13/lean/). Its source library is [`SunflowerLean/`](erdos_20/v13/lean/SunflowerLean/).

[`Erdos20V13Final.lean`](erdos_20/v13/lean/SunflowerLean/Erdos20V13Final.lean) imports the version 13 extensions. It is the entry point to the development; the proof bodies are in the imported modules.

| Source | Result to inspect |
| --- | --- |
| [Erdos20V13Nineteen.lean, line 94](erdos_20/v13/lean/SunflowerLean/Erdos20V13Nineteen.lean#L94) | A 19-member rank-three, three-sunflower-free family with maximum degree at most five has transversal number exactly six. |
| [Erdos20V13FiniteReduction.lean, line 125](erdos_20/v13/lean/SunflowerLean/Erdos20V13FiniteReduction.lean#L125) | I(27) is equivalent to the absence of a specified finite obstruction on `Fin 85`. |
| [Erdos20V13Boundary.lean, line 62](erdos_20/v13/lean/SunflowerLean/Erdos20V13Boundary.lean#L62) | The unrestricted rank-four bound of 80 follows from three explicitly stated inputs. |
| [Erdos20V13Intersecting.lean, line 77](erdos_20/v13/lean/SunflowerLean/Erdos20V13Intersecting.lean#L77) | The residual link of a pair with codegree six is exactly two disjoint triangles. |
| [Erdos20V13Endpoint.lean, line 79](erdos_20/v13/lean/SunflowerLean/Erdos20V13Endpoint.lean#L79) | A concrete 19-member counterexample shows why an inherited endpoint hypothesis cannot simply be weakened. |

For the whole library, use the [884-declaration proof index](erdos_20/indexes/v13-proof-declarations.csv). The [claim-to-root map](erdos_20/v13/evidence/claim-root-map.json) connects the paper's T1–T8 statements to declarations, source lines, and recorded axiom checks. Its source locators retain the original `lean/` prefix and resolve beneath `erdos_20/v13/`.

## Read the result with its hypotheses

In the retained v13 Lean library, the finite-obstruction equivalence is a proved reduction; it does not establish that the obstruction is absent. Its bound of 80 is a proved implication from I(27) and the nonrealizability of Profiles A and B. Those inputs remain unproved within that historical library, which contains no unconditional G(80) kernel root. The later ordinary upper-67 proof follows the separate route described above. The all-rank Erdős–Rado conjecture remains outside both developments.

The v13 source archive also includes deliberate failing tests, mutations, synthetic smoke projects, and one deferred certificate. Their presence records how the work was checked and where earlier attempts stopped. They are classified in the [historical source-file index](erdos_20/indexes/v13-source-files.csv); they are not additional accepted results.

## Check the collection

Clone the repository and check the shipped source inventories with Python 3.9 or later:

```bash
git clone https://github.com/0xagi-bsky-social/A1K.git
cd A1K
python3 erdos_20/tools/verify_inventory.py
```

This checks the retained 348-source inventory, its 21 pinned reference records, the original 178 protected v13 inputs, and the later collection's inventory. It checks file integrity without invoking Lean or downloading the linked references.

The formal project pins **Lean 4.26.0** and its Lake dependencies. With the matching Lean/Lake toolchain installed, the entry-point build is:

```bash
cd erdos_20/v13/lean
lake exe cache get
lake build SunflowerLean.Erdos20V13Final
```

A clean machine needs network access and enough resources to obtain the pinned dependencies and build their imports. The hardened historical replay harness also refers to compiler and cache identities on the original research host; it needs explicit environment configuration before use. Source integrity checks are not a substitute for that build or an independent proof replay.

## Verification records and provenance

The retained [local-check summary](erdos_20/v13/evidence/local-check-summary.json), [axiom audit](erdos_20/v13/evidence/fresh-tail/axiom-audit.json), and [final proof-recheck summary](erdos_20/v13/final-evidence/proof-recheck/summary.json) describe the original runs. The final audit checked **875 public roots**, allowing only `propext`, `Classical.choice`, and `Quot.sound`, against hash-verified project objects and cached dependencies.

This publication preserves that evidence. It does not claim a new full source build, a fresh dependency reconstruction, or independent-host reproduction. Source headers and recorded author credits, including AI-assistance credits where present, remain intact.

## Repository layout

```text
erdos_20/
├── sunflower67-20261025/  Latest ordinary proof, formal interfaces, and exact evidence
├── v13/                  Earlier formal library, retained checks, and reproduction material
│   └── lean/SunflowerLean/
├── v12_audit/            Earlier library, scratch work, and audit fixtures
├── indexes/              Source inventories, proof declarations, and upstream links
└── tools/                Portable source-integrity checker
```

The [transfer summary](erdos_20/indexes/transfer-summary.json) records the counts and dispositions. [Reference links](erdos_20/indexes/reference-links.csv) identify each of the 21 upstream files at an immutable commit.

## Contributions

A useful contribution makes a statement easier to check or supplies a missing proof without weakening its hypotheses. Include the exact declaration, the Lean version, and the commands you ran. When a proposed change affects a conditional result, explain which input it discharges and retain the remaining qualifications. Keep generated caches and personal configuration out of commits.

## License and attribution

A1K contributions are available under [Apache License 2.0](LICENSE). The licensed foundational sources retain their original [NOTICE](NOTICE) and [third-party attribution](THIRD_PARTY_NOTICES.md). Lean and mathlib dependencies retain their own licenses. The Apache-2.0 license does not cover the 21 linked upstream reference files or grant rights to their contents.
