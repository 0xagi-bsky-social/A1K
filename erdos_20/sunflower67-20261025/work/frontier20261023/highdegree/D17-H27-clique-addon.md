# D17 v3: optional literal H27 trace-clique rows

23 October 2026. Ordinary proof-development addendum to `D17-full-model-bridge.md`. The new `degree17_full_projection_v3.py` is copied from frozen v2, SHA-256 `497f71f4fdf555c7456b42123684e7fd5059769f89662c257e2263425798b31a`. This addition does not change the prior mathematical rows or add marked-B4 restrictions. No model, catalogue, solver, or Lean job was executed for this implementation; validation so far is source inspection and AST parsing only.

## Mathematical row and actual-member guard

Let U be a represented set, let x be excluded from every residual member, and let n_s count all actual residual members with exact U-trace s. Let B be a declared list of fixed actual four-sets wholly contained in U∪{x}. A clique C of trace classes is valid when every pair s,t∈C, including s=t, has either a shared represented point or a member B∈B disjoint from s∪t.

In the latter case B is disjoint from every completion of either trace. If two such completions were disjoint, they and B would be three distinct disjoint actual members, a forbidden empty-core sunflower. Therefore the union of these trace classes is intersecting, and H27 gives

    Σ_(s∈C) n_s≤27.

The diagonal test covers multiple completions of a proper trace and the empty trace. Proper traces remain counts, not Boolean variables. The counted family consists only of residual members, so the right side27 needs no subtraction of root cones. A selected residual marker is counted exactly once through its own trace variable. The general proof is `TRACE-H27-CLIQUE-SEPARATION.md`.

## Input and fail-closed checks

The optional CLI argument is `--h27-cliques FILE`, with optional `--h27-cliques-sha256 HASH`. The input schema is `trace-h27-clique-discovery-v1`. A manually selected subset such as `degree17_full/P10-H0-H27-top32.json` can retain this schema; its exact bytes become the row-data dependency. Neither the input's numerical discovery weights nor its claimed prior validation, source receipt primal, search completeness, or forbidden-trace premises are used to justify the row.

The loader requires threshold27 and a nonempty explicit row list. It verifies the declared separator and ordinary-note hashes against the current source files. The receiving validator then requires:

1. The same literal root-link kind. The excluded point list must be exactly `[15]`, the receiving residual root. Represented labels must be distinct, sorted, and valid receiving labels.
2. Every declared fixed member is a distinct four-set in the receiving `fixed` list: complete root cones plus the actual selected marker and actual assigned Z members. A member merely allowed by a positive variable upper bound is not actual. Each witness must lie wholly in the source represented universe plus the excluded root.
3. Each row has upper27, distinct nonnegative integer trace masks of size≤4, and no point outside the source represented universe. Duplicate whole rows are rejected as malformed input. Every unordered trace pair including self is rechecked with literal bit intersections and the validated actual witnesses.
4. The permitted universe relation is either exact equality or the explicit root-only refinement below. Arbitrary relabelings, deletions, or other universe changes fail. A marker-dependent clique cannot be silently transferred to a branch where its witness is absent.

These checks validate all rows before their coefficients are used. No row is admitted merely because its sampled discovery weight exceeds27. Zero-upper-bound trace classes may appear; their coefficient contributes zero to an actual solution and does not weaken the mathematical argument.

## The one supported refinement

Root-only cliques discovered on the complete core U may be used in a receiving mixed-three-marker branch whose universe is U′=U∪{e}, where e is that actual marker's one exterior point. The source represented list must be exactly the receiving complete core, the receiving universe must add exactly its one canonical marker point, and every declared source witness must be a receiving root cone.

The implemented row is

    Σ_(t⊆U′, |t|≤4, t∩U∈C) n_t≤27.

Each actual residual has one fine trace t and one coarse trace t∩U. Thus this sum is exactly the coarse clique's actual member count; every exterior completion is retained. Simply preserving only the old masks would not express this equality. The coarse pair checks suffice because their witnesses lie in U∪{x}, and the added represented point cannot change their disjointness or shared-point proof. This supports transfer from an unmarked root-only clique file to selected marker cases of the same geometry without introducing new fixed-member premises.

No coarsening or arbitrary permutation is implemented. To use other labels or marker witnesses, supply a new literal file whose data pass the receiving checks.

## API, receipt identity, and replay contract

The previous eight-item return value of `build` is unchanged. The new trailing keyword arguments are

    build(..., h27_cliques=path, h27_cliques_sha256=expected_hash)
    run(..., h27_cliques=path, h27_cliques_sha256=expected_hash)

`h27_clique_input(path, expected_sha256)` returns the parsed payload and a dependency dictionary. The receipt stores this dictionary as `h27_cliques`, or `null` when disabled. Its fields are:

    path, sha256, schema, source_kind, source_case,
    represented_points, excluded_points, fixed_members,
    clique_row_count, sources, transfer_policy.

`sources` binds both the separator file and the general ordinary H27 note, each by path and SHA-256. The full dictionary occurs in the literal branch premises and as an explicit key in the hashed receipt identity. The imported source list additionally binds this addendum, the general H27 note, the separator, and the frozen v2 adaptation source. The data file's exact SHA-256, rather than a path alone or a hash claimed by discovery, determines the used rows.

For each new row the label is `('external-literal-H27-trace-clique', row_number, row_mask_hash)`. Coefficients are rebuilt by looking up the receiving trace masks; discovery column indices are never used. Row order follows the explicit file list. The row-mask hash is the SHA-256 of the sorted mask tuple serialized as compact JSON.

A replay should first check the receipt's `h27_cliques.path` against `h27_cliques.sha256`, then call `build` with that file and expected hash. The loader itself verifies the hash before reconstruction and performs the complete literal witness validation. `premises(..., h27_cliques=dependency)` takes the dependency dictionary, not the file path, so it can reproduce the recorded literal premises. The receipt identity includes the dictionary under its own `h27_cliques` key in addition to its presence in `literal_premises`.

`run` pins the input hash before building and verifies unchanged input/dependency content before writing a receipt. The `--build-only` path applies the same stability check. Catalogue mode rejects a supplied clique option rather than pretending that catalogue output validates its rows. Any resulting upper bound or infeasibility claim still requires exact replay against this new source and complete matrix; the addon itself establishes no numerical D17 exclusion.

## Prepared input and current validation boundary

The top32 file currently has32 distinct row lists, kind `P10-H0`, represented points0,…,11, and excluded point15. Its declared separator/note hashes agree with the observed files. This was a static JSON inspection only; the v3 validator and model have not been executed. An AST parse of the new source succeeded. The coordinating task is responsible for choosing and running the bounded discovery cases and later exact arithmetic replay.
