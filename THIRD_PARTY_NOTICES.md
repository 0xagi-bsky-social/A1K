# Third-party sources and license scope

The root Apache-2.0 license covers A1K contributions. It does not replace the
terms attached to third-party material, confer ownership of that material, or
grant rights that its authors have not granted.

## sunflower-lean foundations

The `Basic.lean` and `Spread.lean` modules in the v13 project, and their preserved
v12 copies, originate in [SproutSeeds/sunflower-lean](https://github.com/SproutSeeds/sunflower-lean).
The source comments credit Cody Mitchell and Claude (Opus). These original four files
match the upstream Git blobs at commit
`6b7f3dcc19a111cf772a630092c48567ac1b51d8`:

| Copies in this repository | Upstream file | Git blob SHA-1 |
| --- | --- | --- |
| `erdos_20/v13/lean/SunflowerLean/Basic.lean`; `erdos_20/v12_audit/archive/erdos20-lean-v12/SunflowerLean/Basic.lean` | `SunflowerLean/Basic.lean` | `6f0ea3092d17a37f31bbbbf1fa5c524ed4849902` |
| `erdos_20/v13/lean/SunflowerLean/Spread.lean`; `erdos_20/v12_audit/archive/erdos20-lean-v12/SunflowerLean/Spread.lean` | `SunflowerLean/Spread.lean` | `ac9c8c69ef448aa4a7a9ca999615f4c14994fc9f` |

Their Apache-2.0 license and original attribution notice are preserved verbatim
in [`LICENSES/sunflower-lean-Apache-2.0.txt`](LICENSES/sunflower-lean-Apache-2.0.txt)
and [`LICENSES/sunflower-lean-NOTICE.txt`](LICENSES/sunflower-lean-NOTICE.txt).
The NOTICE reads:

```text
sunflower-lean
Copyright 2026 Cody Mitchell (Fractal Research Group)
```

See the pinned upstream [license](https://github.com/SproutSeeds/sunflower-lean/blob/6b7f3dcc19a111cf772a630092c48567ac1b51d8/LICENSE)
and [NOTICE](https://github.com/SproutSeeds/sunflower-lean/blob/6b7f3dcc19a111cf772a630092c48567ac1b51d8/NOTICE).

The 19 October project and 20 October release retain four further unchanged copies of these two modules under `erdos_20/sunflower67-20261025/work/frontier20261019/lean/SunflowerLean/` and `erdos_20/sunflower67-20261025/work/frontier20261020/release-formal/source/SunflowerLean/`. The same license, notice and attribution apply to those copies.

## MIT-licensed construction reference

The later capacity comparison includes `Bprime.txt` and `verify_bprime.py` from [xSyllaa/sunflower-pendant-chain](https://github.com/xSyllaa/sunflower-pendant-chain), pinned to `8e21d0287711b4f0bfc23e9443523e2aa472cca1`. Their original MIT license, copyright notice and retrieval provenance accompany them in [`capacity/upstream/`](erdos_20/sunflower67-20261025/work/frontier20261023/capacity/upstream/). This reference concerns a separate construction comparison; its presence does not extend the upper-67 theorem or its formal assurance.

## Linked October structural foundation

The upper-67 proof imports specified structural results and finite packages from [aconsciousfractal/Four-Uniform-Three-Sunflower-Bound](https://github.com/aconsciousfractal/Four-Uniform-Three-Sunflower-Bound), pinned to `90c03c79bcf44eb8f61dff1b86091b822cc4cd3c`. No project-wide redistribution license was found in that checkout. Its original files and byte-identical mirrors are linked with immutable URLs, sizes and hashes in the [later external-reference index](erdos_20/indexes/sunflower67-external-references.csv), rather than redistributed. The locally authored import ledger, replay receipts and mathematical bridges are retained. Readers need to obtain the pinned upstream sources separately for checks that import them.

Fetched third-party full text and source-response blobs are also represented by hash and source records when redistribution rights are not established. A retrieval record is not a grant of rights, endorsement, or authentication of a historical computation. The source-inspection notes retain the limits of the H27 provenance audit.

## Linked sunflower-paper reference sources

The source inventory identifies 21 Lean reference files from
[bogdan27182/sunflower-paper](https://github.com/bogdan27182/sunflower-paper),
commit `d4d5723267c662291efdadfa6e7061d919e76fa9`.
They are reference sources, separate from the v13 `SunflowerLean` proof library.
These 21 files are linked at their immutable upstream locations rather than
redistributed in A1K. The links, original paths, sizes, and SHA-256 hashes appear
in [`erdos_20/indexes/reference-links.csv`](erdos_20/indexes/reference-links.csv).

The pinned repository's [licensing statement](https://github.com/bogdan27182/sunflower-paper/blob/d4d5723267c662291efdadfa6e7061d919e76fa9/LICENSES/README.md)
does not grant a project-wide license for its original code. Its license files
apply to named third-party SAT and graph tools, not to these Lean modules.
The A1K Apache-2.0 license does not apply to those linked files. Their authors
retain their rights. Linking to the sources does not grant permission to reuse
or relicense their contents.

## Lean and mathlib

The developments depend on Lean and mathlib through their pinned toolchain and
Lake manifests. Dependency packages and compiled caches are not included in this
repository. Those dependencies retain their own licenses. mathlib's
[Apache-2.0 license](https://github.com/leanprover-community/mathlib4/blob/v4.26.0/LICENSE)
is independent of the license for A1K contributions.

Existing source headers, author credits, and provenance records have been
retained. Attribution identifies an origin; it does not imply endorsement by
the upstream authors or proof of any theorem beyond the recorded verification.
