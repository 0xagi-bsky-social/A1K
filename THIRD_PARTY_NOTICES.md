# Third-party sources and license scope

The root Apache-2.0 license covers A1K contributions. It does not replace the
terms attached to third-party material, confer ownership of that material, or
grant rights that its authors have not granted.

## sunflower-lean foundations

The `Basic.lean` and `Spread.lean` modules in the v13 project, and their preserved
v12 copies, originate in [SproutSeeds/sunflower-lean](https://github.com/SproutSeeds/sunflower-lean).
The source comments credit Cody Mitchell and Claude (Opus). These four files
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
