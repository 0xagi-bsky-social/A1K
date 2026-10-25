# H7 equality and explicitly selected extra actual members

23 October 2026. Ordinary proof development, conditional on the stated earlier exclusions and structural imports. This note gives an independently checkable fifteen-row inequality and a two-case consequence. It does not establish either case's impossibility or close H7 or degree17.

## Literal branch and equality

Let F be a finite simple four-uniform sunflower-free family, including the empty-core prohibition, with |F|≥68 and a point x=15 of degree17. Assume the global degree bound17, the μ41 prior structural package, and the complete root link P10 on Y={0,…,5} disjoint from H7 on Z={6,…,12}. The latter seven triples are

    689, 68(10), 69(10), 78(10), 79(10), 67(11), 67(12).

The twelve separate P10 component exclusions supply absence of every internal Y four-set. Assume also the completed exclusion of the other seventeen internal-Z marker orbits. Their 33 four-sets are exactly C(Z,4) minus the two members of IZ13,

    {7,8,11,12}, {7,9,11,12}.

Mark M={7,8,11,12} as actual. The selected equality receipt is
`degree17_full/P10-H7-IZ13-internal-Z-stage2-v4-9ff2bf3fd06c.json`, SHA-256
`0d4b5004a86f70dfe0c90c02dafd3346499f4c31e6e84fb76589bf239ae3fc68`.
Its frozen source v4 is
`a1beae56f60205a48442a1c6a31d2148557443511fb119a1936ffda8578bebf2`.

Write r=|F\F_x| and let n_S count residual members with exact core trace S⊆Y∪Z. Such counts include arbitrary exterior multiplicities. The checker `check_d17_h7_equality.py` imports no producer or numerical package: it rebuilds the following fifteen valid inequalities directly from literal sets, subtracting only complete-root-cone offsets.

| Rows | Number | Residual right-hand sides |
|---|---:|---:|
| Triple-incidence cap2 on each of the ten P10 blocks | 10 | 1 each |
| Triple-incidence cap2 on {8,9,10} | 1 | 2 |
| Exact pair {7,11} at R={15,6,7,11} | 1 | 3 |
| Crowding26 on the three exact singleton classes 7,11,15 at R | 1 | 16 |
| Exact singleton12 at {15,6,7,12} | 1 | 10 |
| Triangle-plus-path hub6 degree minus its three internal cover completions≤15 | 1 | 10 |

Their right-hand sides sum to51. For the 1,093 subsets S of the thirteen-point core of size at most4, 517 traces are absent by Y-emptiness, the assumed 33 Z exclusions, or a literal sunflower with M and a root cone. Every other trace has coefficient at least1 in the summed inequality: 503 have coefficient1 and 73 have coefficient2. These are finite integer checks, not floating-point evidence. They imply

    r ≤ Σ_S q_S n_S ≤ 51.

The marker has coefficient1; the independent box correction is0, and the receipt's fifteen nonzero weights are all exactly its scale10^10. There are no equality-row weights or local-selector coefficients in this inequality. Thus the literal check suffices for this bound without rebuilding the unused local-selector columns. Its scope still includes the prior theorems behind the rows and the preceding exclusions behind zero traces.

Since r≥68−17=51, equality holds throughout. Every one of the fifteen positive-weight inequalities is tight. In particular the actual exact-pair count p_{7,11}(R) equals3; no root cone contributes to this class, so this is also its residual count.

## The forced triangle and its two surviving vertices

Write the three distinct pair-class members as {7,11}∪U_i, where each U_i is a two-set avoiding R. Two disjoint U_i would give, together with R, a sunflower with core{7,11}. Three edges U_i with a common vertex would themselves give a sunflower. Three distinct pairwise-intersecting edges without a common vertex are the edges of a triangle.

M supplies its edge{8,12}. Consequently there is a single point t outside R∪{8,12} such that both

    B_t={7,8,11,t},     C_t={7,11,12,t}

are actual. Among represented core points, t lies in Y or is9 or10. The choice9 forces the already absent B_9, mask2944; choice10 forces the already absent B_10, mask3456. The complete automorphism group of P10 has order60 and is transitive on Y; it acts trivially on Z and preserves the Y-empty and all Z-exclusion premises. Thus all choices t∈Y reduce to t=0. Every point outside the core and root can instead be relabelled13, without restricting any other exterior point. The two remaining branches select

    t=0:  [[7,8,11,0], [7,11,12,0]], masks2433,6273;
    t=13: [[7,8,11,13], [7,11,12,13]], masks10624,14464.

No near-family B4 assumption is needed for this elementary triangle step. Neither branch is an assigned-Z pattern: every internal membership beyond the earlier 33 exclusions remains free. The original IZ13 marker is still present in both branches.

## v5 family-to-model extension

`degree17_full_projection_v5.py` is a new source copied from frozen v4. Its trailing `extra_members` argument and CLI `--extra-members` accept an explicit list of four-label lists or integer masks; normalized sorted masks are recorded. Invalid or duplicate members, root-containing members, and points beyond the one canonical extra label are rejected. A selected member conflicting with an absence premise or forming a literal sunflower is rejected by the existing model construction.

Let U be the complete root core together with all selected actual residual members (the original marker, supplied extras, and any independently requested assigned-Z members). The represented size n is computed from this entire support. It is13 in the t=0 branch and14 in the t=13 branch. Every represented point is used by an actual member; the minimum-used-degree7 rows therefore remain applicable. Other points are still arbitrary and unrepresented. Trace bounds 27/17/6/2/1 and the family map retain the same justification as in `D17-full-model-bridge.md`.

Each selected four-set has exact full-trace lower bound1. All are included in the common `fixed` list before sunflower pruning and every fixed-member calculation. Consequently each new actual member is an anchor for disjoint-H27, μ41, exact singleton/pair/triple caps, pairdegree19, crowding26, and all ordered two-anchor triangle rows. All pairs of actual fixed members are available for B4 witnesses and all relevant fixed pairs are used for trace sunflower exclusions. Central local-catalogue pruning uses the newly enlarged B4 witness list. Only root cones are constant offsets; added members are residual trace variables and are never subtracted again.

The seventeen central-root local catalogues remain catalogues of their original root anchors. This is a valid relaxation; no claim that a separate local catalogue is imposed at every new anchor is needed. Existing C5/P5/hub rows retain their literal complete-root-link hypotheses and exact internal trace indices. Core singleton-pool rows retain the same component supports; a new represented exterior point only refines their counted traces.

Optional H27 rows are revalidated with the entire receiving `fixed` list. Same-universe source witnesses must be selected actual members. A source on the core may lift to one newly represented point only with root-cone witnesses, by restriction of fine traces; this remains the existing conservative v4 transfer policy. Extra members do not authorize another source transfer or a second new point.

The receipt and premise identity both record `extra_members`, `selected_actual_members`, and `represented_points`; the literal-premise branch dictionary repeats them. This note and v4's bytes are source dependencies. A v5 exact replayer must reconstruct these lists and support independently, pass the extras into `build`, use all selected actuals for independent triangle/B4/H27 verification, and include all three fields in the premise fingerprint. Frozen v2/v3/v4 replayers do not acquire v5 support merely by accepting a new hash.

The existing complete root-link marker catalogue remains unchanged: its original orbit labels describe the first marker, while explicit extras are additional branch premises. A later coverage assembly must separately bind the equality extraction, all earlier excluded orbits, and both extra-member leaves. No new solver or full-model replay is part of this note.
