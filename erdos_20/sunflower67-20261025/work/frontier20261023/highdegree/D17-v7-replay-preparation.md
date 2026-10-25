# Prepared v7 phase-one and exact-replay adapters

23 October 2026. Prepared source only: AST syntax was checked, but neither
file was imported or executed, and no model construction, solver or replay
was run. Older sources and adapters are unchanged.

Frozen model: `degree17_full_projection_v7.py`, SHA256
`f8108979ae0c461d8e897b660e5d96565fd9a58afbe7465d0839dcf25c990de3`.

New phase-one adapter: `degree17_full_phaseone_v7.py`, SHA256
`939f32062388b52f32b9dd5588823bf61f311af82b96767ddbd37f67b9a6299e`.
It accepts only a status2 receipt for those exact v7 model bytes, retains
all branch and extra-member premises, and limits its single invocation to
at most30 seconds. It preserves the v6 original-box/slack formulation and
exact rounded integer arithmetic diagnostic.

New solver-free replayer: `replay_degree17_full_v7.py`, SHA256
`a80e604393bc2a9d76b0e3f2ed0c35b459762178e1a7424415310d276d72fcfb`.
It retains support for prior pinned sources and adapters, with v7 linked
only to the new exact phase-one hash. The v6 whole-low-Y H27 validator also
runs on v7. Before the full integral-model scan and weighted arithmetic,
the new validator independently checks:

* the literal complete canonical P9 and eight disjoint-support K triples;
* its eleven triple transversals, absence of one/two-point covers, and
  presence of an H block in every internal four-set;
* every eligible fixed actual Q outside x+Y, with no promotion of an
  unselected trace to an actual member;
* the disjoint and meeting root-cone offsets, every residual coefficient,
  the absence of selector coefficients, both right sides, and exact
  coverage of all eligible anchors.

The ordinary complement note and the row-projection note are pinned to
exact hashes, in addition to the usual receipt dependency registry.
This replayer still uses the producer's build() for the full model. The
new row check is independently reconstructed, while the underlying
complement theorem and HP15 remain explicit ordinary/imported premises.
No independent reconstruction of all model mathematics or Lean result is
claimed. Each future invocation accepts one receipt and at most30 seconds.
