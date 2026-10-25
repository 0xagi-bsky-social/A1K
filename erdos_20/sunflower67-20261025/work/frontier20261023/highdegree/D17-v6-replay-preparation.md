# D17 v6 certificate helpers prepared without execution

23 October 2026. Source preparation only. The frozen v1--v5 models and
helpers are unchanged. None of the new modules was imported or executed;
only their Python source syntax was parsed with `ast.parse`.

`degree17_full_phaseone_v6.py` is the v5 phase-one adapter with its
model filename and exact SHA pin moved to v6. It accepts one numerical
status2 input receipt, reproduces its selected actual members and support,
and rebuilds the same hash-bound model. Its time limit remains at most30
seconds, and the output remains a tagged zero-objective integer-box
certificate with an immutable new receipt path.

The pinned model SHA256 is

    8f43465ef15e09ba5ea8f472a4382f844ccb3ebeface8841f7963625f65e8138

The new phase-one helper SHA256 is

    dbd6cc300ab8a94b060521e868786359152327486d781eace448dda968730967

`replay_degree17_full_v6.py` adds these exact pins while retaining explicit
support for older frozen versions. The source-to-phase-one association is
checked by a version-specific SHA set: the new adapter can only certify
the new v6 model, and v5 remains pinned to v5. All previous exact replay
checks, actual-member decoding, triangle/B4 rows, external H27 cliques,
box validation, integer accumulation, dependency binding and deadline
guards are retained.

Before scanning all model entries and before weighted certificate
arithmetic, the new replayer independently reconstructs the built-in
`Y-at-most-one-H27` row as follows:

1. Decode the six actual Y points, distinguished root, and all17 recorded
   root-link triples using ordinary sets. Identify its nine or ten Y
   blocks and restore their actual root cones.
2. For each of the22 subsets of Y of sizes0,1,2, find and check an actual
   root cone avoiding that subset. The producer's avoidance, geometry,
   clique and row-construction helpers are not called for this check.
3. Check all28 unordered pairs with repetition of the seven possible
   zero/singleton Y classes, including every diagonal, against that table.
   Because the witnesses use only Y and the root, the table covers every
   exterior completion of every root-avoiding trace in the row.
4. Reconstruct every expected trace coefficient, require exactly one
   correctly labelled row, reject selector terms, and compare the complete
   sparse row and RHS27. The root-cone offset must be zero.

Replay output records the literal table, its digest, class-pair coverage,
the implied number of covered trace pairs including diagonals, and the
full row digest. The proof that this class coverage applies on arbitrary
support is `D17-Y-at-most-one-H27.md`, which the v6 model also includes in
its hash-bound dependency registry. H27 itself remains an imported premise.

This strengthens one independently checked portion of the model; overall
matrix reconstruction still uses the same frozen producer. No independent
reconstruction of every model row, Lean verification, successful execution,
or completed branch proof is claimed by this preparation note.
