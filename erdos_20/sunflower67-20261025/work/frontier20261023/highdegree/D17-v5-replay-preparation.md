# Degree17 v5 certificate adapter preparation

23 October 2026. Ordinary implementation development; prepared with source inspection and AST parsing only. No producer import, model build, solver or full replay was executed while writing these adapters.

The new `replay_degree17_full_v5.py` copies frozen v4's exact integer-box replay and adds the one inspected v5 producer SHA
`bee8278d87557a3f979d7c69022d62d775e74f093cb87ece2c935e6f1acd1210`.
The original, v2, v3 and v4 producer adapters remain present. The frozen v4 replayer is unchanged.

The v5 adapter requires the new explicit normalized mask list `extra_members`. Without calling the producer's normalization helpers, it reconstructs the ordered deduplicated selected family from the marker, sorted extras and any assigned-Z members. It verifies four-uniformity, avoidance of root15, canonical core support with at most its one extra point, the receipt's `selected_actual_members` and `represented_points`, and absence of a literal sunflower among fixed actual members. All three metadata fields enter the reconstructed premise fingerprint. The extra-members argument is passed into both `premises` and `build`.

After shared-producer model reconstruction, an independent literal-set check rebuilds the complete ordered trace domain and all its boxes, including selected membership lower bounds, assigned internal bounds, component emptiness, forbidden traces and fixed-pair sunflower pruning. It also reconstructs every actual-anchor disjoint-H27, μ41, exact singleton/pair/triple-cap, pairdegree19 and crowding26 row, checking its full coefficient vector and root-cone-only offset. Its evidence appears in `extra_actual_member_validation`.

The existing independent triangle and B4 checkers now receive the same complete selected family, including both added actual members. B4 pruning still decodes the final local selector feature equations independently. H27 validation likewise reconstructs the entire receiving actual family and represented support. Its conservative core-to-one-point transfer still requires root-cone witnesses; it now permits that one actual point to come from an extra member rather than requiring it in the original marker.

All existing exact integer matrix, finite-box, source/dependency, P10 component exclusion, sparse-dual and all-column checks remain. The resulting assurance is exact arithmetic for a hash-bound necessary relaxation with the stated independent row/geometry checks, not independent reconstruction of every model row or a proof of its imported structural assumptions.

The separate new `degree17_full_phaseone_v5.py` pins that same v5 source, passes the recorded extra members into its unchanged model, and checks selected-support metadata and all model dimensions/catalogue sizes. It preserves original receipt metadata while replacing the numerical status and dual diagnostic. Its SHA is
`957d9fd1e1fa162a3f3a18a1937a5cc613078552c4ca607dc76c60d67cb568f8`.
The old phase-one producer remains unchanged. The new replayer explicitly binds both frozen phase-one producers and requires the v5 helper for a v5 source. Zero-objective certificates retain the original status2 input/hash and must replay H plus box correction strictly below0.

The H7 equality extraction and the two-branch covering argument are separate ordinary evidence in `D17-H7-equality-extra-members.md` and the root-generated `degree17_full/H7-IZ13-equality-extraction.json`. The prepared replayer does not by itself bind the earlier seventeen internal-orbit exclusions or conclude whole H7 coverage.
