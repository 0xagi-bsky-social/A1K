# A1K

**Lean sources and research evidence for Erdős problem 20.**

A1K publishes the formal developments behind its research on sunflower-free set families. This collection brings the current version 13 library, its earlier working sources, and the recorded checks into one place. Readers can inspect a theorem, follow its dependencies, and compare the formal statement with the claims in the paper.

The accompanying paper is [Transversal Six, Finite Obstructions and Boundary Profiles in Rank-Four Sunflower-Free Families](https://a1k.ai/agentic-math/rank-four-sunflower-free-families). The repository preserves the source statements and their qualifications, including the inputs that remain open.

## What is here

Every Lean source file in this repository lives under [`erdos_20/`](erdos_20/).

| Collection | Count |
| --- | ---: |
| Current v13 modules | **155** |
| Modules containing theorem or lemma proofs | **149** |
| Public theorem roots in the recorded audit | **875** |
| Current theorem/lemma declarations, including nine private helpers | **884** |
| Lean files distributed across the current library and retained history | **348** |
| Upstream reference files provided as pinned links | **21** |

The last two rows account for the **369 Lean files** in the original source inventory. The 21 reference files are linked to their upstream revision because their project does not grant an open-source license. All 348 distributed Lean files retain their original bytes. Older copies are kept in their historical locations rather than merged into the current library.

## Start with the proofs

The current project is [`erdos_20/v13/lean/`](erdos_20/v13/lean/). Its source library is [`SunflowerLean/`](erdos_20/v13/lean/SunflowerLean/).

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

The finite-obstruction equivalence is a proved reduction. It does not establish that the obstruction is absent. Likewise, the bound of 80 is a proved implication whose inputs are I(27) and the nonrealizability of Profiles A and B. Those inputs remain unproved in this collection. G(80) and the all-rank conjecture remain open locally.

The source archive also includes deliberate failing tests, mutations, synthetic smoke projects, and one deferred certificate. Their presence records how the work was checked and where earlier attempts stopped. They are classified in the [source-file index](erdos_20/indexes/lean-source-files.csv); they are not additional accepted results.

## Check the collection

Clone the repository and check the shipped source inventory with Python 3.9 or later:

```bash
git clone https://github.com/0xagi-bsky-social/A1K.git
cd A1K
python3 erdos_20/tools/verify_inventory.py
```

This checks all 348 source hashes, the 21 pinned reference records, and the original 178 protected v13 inputs. It checks file integrity without invoking Lean or downloading the linked references.

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
├── v13/                  Current library, retained checks, and reproduction material
│   └── lean/SunflowerLean/
├── v12_audit/            Earlier library, scratch work, and audit fixtures
├── indexes/              Source inventory, proof declarations, and upstream links
└── tools/                Portable source-integrity checker
```

The [transfer summary](erdos_20/indexes/transfer-summary.json) records the counts and dispositions. [Reference links](erdos_20/indexes/reference-links.csv) identify each of the 21 upstream files at an immutable commit.

## Contributions

A useful contribution makes a statement easier to check or supplies a missing proof without weakening its hypotheses. Include the exact declaration, the Lean version, and the commands you ran. When a proposed change affects a conditional result, explain which input it discharges and retain the remaining qualifications. Keep generated caches and personal configuration out of commits.

## License and attribution

A1K contributions are available under [Apache License 2.0](LICENSE). The licensed foundational sources retain their original [NOTICE](NOTICE) and [third-party attribution](THIRD_PARTY_NOTICES.md). Lean and mathlib dependencies retain their own licenses. The Apache-2.0 license does not cover the 21 linked upstream reference files or grant rights to their contents.
