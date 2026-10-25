# D17 v8 literal-profile model and adapters prepared

23 October 2026. Source preparation only. All three Python files passed
AST syntax checks; none was imported or executed. No model build, solver,
replay or Lean process was run. All v1--v7 sources and adapters are unchanged.

Exact new files and SHA256:

* `degree17_full_projection_v8.py`:
  `c7cf58b6d2bc9e523d729dbc5a2ae9aeb83164fabed3b4b1211b30d6e889f245`
* `degree17_full_phaseone_v8.py`:
  `b93524d1f990f5550e28d306e0d3b34c22f0826c8b26ec6072860f6e7db26654`
* `replay_degree17_full_v8.py`:
  `c7dbab0c3d483c6e610b5ccd5ce049b1f980c668789647c099bf551aa886ecb8`
* Ordinary bridge `P9-literal-complement-profile.md`:
  `1a8556b569ca5c6816a4ed2821dfe4cb280bdb3b0eeeb6b890eb034e4aa1d410`

The model replaces v7's uniform cap22/mu46 rows by the minimum applicable
literal profile for each fixed actual Q outside x+Y. It preserves every
other v7 row. P10 branches receive no profile rows. The profile uses the
exact surviving K cones and their common intersection; it does not import
cap16 no-P9, NO46, or any lower-root result into the D17 model.

The phase-one adapter is pinned exclusively to v8 and retains one-case,
30-second limits, exact original metadata, original boxes and signed
equality weights. The replayer accepts the new exact model and phase-one
hashes while retaining prior pinned versions. Before weighted arithmetic,
it independently reconstructs canonical P9/transversal facts, all selected
actual anchors, every surviving K cone, the common intersection and all
applicable bound candidates. It compares the literal profile metadata in
the row labels and every coefficient/RHS/root offset. The complete new
ordinary bridge is separately hash-pinned; old v7 bridge pins are retained.

The future replay still reconstructs the overall model using its exact
producer build(). The profile validator is independent of that producer's
profile arithmetic; it is not an independent reconstruction of every
unrelated model row or a formal proof of HP15 and other imported inputs.
