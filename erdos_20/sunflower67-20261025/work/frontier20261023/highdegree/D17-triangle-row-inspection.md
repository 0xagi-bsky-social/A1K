# Degree17 generic triangle rows: separate derivation and replay preparation

23 October 2026. This is a second ordinary derivation and static source
inspection, performed after freezing `degree17_full_projection_v2.py`.
No model, catalogue, solver, certificate replayer or finite census was
executed. The earlier hashed bridge and all producer sources remain
unchanged.

The inspected v2 SHA256 is

    497f71f4fdf555c7456b42123684e7fd5059769f89662c257e2263425798b31a.

## 1. Derivation from the complete family, before any projection

Take actual distinct members R,M with R intersect M={h,m}. For k in
R minus M, write R={a,h,k,m} and M={h,b,c,m}. All six points are
distinct. Define

    s = #{Q in F:Q intersect R={m}},
    p = #{Q in F:Q intersect R={k,m}},
    M'=(M minus{h}) union{k},       j=1[M' in F].

The exact singleton and pair caps give s<=10,p<=3. When s>=8, B4
makes the near part of the complete link at m intersecting relative
to R minus{m}. If p=3, remove{k,m} from those three members. Their
distinct two-sets avoid R and are pairwise intersecting, because R
would complete a sunflower for a disjoint pair. They cannot share a
point, because their three members would then form a sunflower with
that point added to{k,m}. Thus they are a triangle.

The known near triple M minus{m}={h,b,c} must meet each near triple
formed by adjoining k to one of the triangle edges. The edges avoid h
and k is distinct from h,b,c, so every edge meets{b,c}. A triangle's
edges can all meet this two-set only if both b and c are triangle
vertices. Its edge{b,c} gives the actual member M', hence j=1. We have
p<=2+j. Combining with s<=10 gives s+p-j<=12. For s<=7 the bounds
p<=3 and j>=0 give the stronger value10. Consequently

    s+p-j <= 12

holds unconditionally once R and M are actual. This re-derives the
general lemma of `D18-I06-triangle-closure.md`; it does not use an
I06 pattern, a degree cap, mu41 or an I7 classification.

## 2. Split into fixed root cones and residual variables

Let S_x be the complete root star and C the represented actual-point
set excluding x. Every fixed actual anchor is contained in C union{x}.
Residual members have exact C-trace U and are counted by n_U. Define

    a_U = 1[U intersect R={m} or U intersect R={k,m}],
    o = #{B in S_x:B intersect R={m} or B intersect R={k,m}}.

Because R has no unrepresented point, this is an exact decomposition

    s+p = o + sum_U a_U*n_U.

Selected residual anchors are included in n_U, with lower bound1;
only root cones belong in o. This remains true if R is itself a
residual marker and if one or both anchors contain the represented
exterior point. Arbitrary unrepresented exterior multiplicities do
not affect any intersection with R.

There are exactly two ways to represent j:

| Companion | Membership | Projected inequality |
|---|---|---|
| x in M' | j=1[M' in S_x], by completeness | sum a_U*n_U <=12-o+j |
| x notin M' | j=n_M', because M' is a represented four-set | sum a_U*n_U-n_M' <=12-o |

For a residual companion, M' intersect R={k,m}. Thus a_M'=1, and
the final coefficient of n_M' is **zero**. Setting that coefficient
directly to-1 would be incorrect. For a present root companion, the
same cancellation occurs between its contribution1 to o and the
constant +j on the right. An absent root companion has j=0. The
complete root link decides both possibilities even when M' mixes
components or uses a represented exterior point.

The anchors R and M themselves contribute zero to s+p: their traces
are R and{h,m}, respectively. Other selected actual members may
contribute, and the formula properly leaves them among the variables.
No selected residual is counted in both a variable and a fixed offset.

## 3. Literal v2 source inspection

The loop visits every ordered pair in `fixed`, retaining precisely
two-point intersections. It visits each shared m, determines the
other shared h, and visits both k in R minus M. The companion mask
`(M ^ hbit) | (1 << k)` removes an actually present h and adds an
actually absent k, preserving cardinality4. The union of R and M
has six points, so no implicit label collision is possible.

Its trace coefficient test is exactly the two categories above.
`offset` sums those same categories over `g['star']` only. If the
companion contains x, `rhs += int(companion in g['star'])` installs
the correct known constant. Otherwise `index[companion]` exists,
because the companion lies in C and has size4; the update
`cs[j] = cs.get(j,0)-1` cancels its existing pair coefficient.
The row insertion drops zero entries. All row coefficients and right
sides are integral.

The fixed list consists of the seventeen actual cones, the actual
marker if any, and every assigned-present Z internal, deduplicated
among selected residuals. Free members are never included as actual
anchors. This checks cone/cone, cone/residual, residual/cone and
residual/residual ordered pairs. I found no mathematical or sign
error in these rows.

This is independent re-derivation by the same agent, not an independent
reviewer or an execution test. The additional replayer check below
uses a separate set-based reconstruction of these particular rows.

## 4. Prepared full-model replayer

`replay_degree17_full.py` was adapted from the unchanged
`replay_degree18_p10.py`, hash

    d69a6ef6c4ff9096af11af947dd8ac5aed3f82ec0fcba72bf5d4a42b725864bd.

It accepts the two inspected source hashes: original
`3d79ea4a0755f59aa8107c89d773600bc0965aa751772c337c3431c3a7caff52`
and v2 above. Future source hashes require explicit adapter inspection.
It requires the exact eleven D17 kind names, root17, cap17, mu41 and
target51. It uses the same hashed producer `build()` for reconstruction,
blocks producer/solver entry points, and checks all integral matrix
entries, right sides and finite box endpoints, not only weighted rows.
It binds exact geometry, literal premises, branch switches and all
producer dependency hashes before checking the integer weighted bound.

The ordinary trace objective compares its exact box-corrected numerator
with51 times the positive integer scale. The explicit zero-infeasibility
protocol compares with0, requires objective='zero', checks the original
status2 receipt and unchanged model metadata, and hash-binds the separate
named D17 phase-one producer. No D17 phase-one producer or phase-one
receipt is asserted to exist by this prepared adapter.

For v2, `validate_triangle_rows` decodes masks into actual point sets
and constructs the entire expected ordered-pair/m/k collection. It
checks every sparse triangle coefficient and right side against the
set-based formulas in Section 2, including constant root membership,
residual-companion cancellation and fixed offsets. It also checks
coverage and duplicate labels. This is a separate reconstruction of
the added rows; other rows remain shared-producer reconstruction.

## 5. Separate binding of the completed P10 dependency replays

The original hashed full-model producer records the twelve component
receipts and their reported gaps. The new replayer additionally requires
and binds the existing twelve successful exact component-replay records,
without modifying the producer, its old bridge, or those records.

The pinned summary is `degree17-replay/P10-nonempty-summary.json`, hash

    d130fb5c8f164e4ab6a164e60bd1c2e8f41021da82f48195255a3cc11690711c.

Its source and checker are pinned as follows:

    degree17_component.py
    1e3eaa89225246bb695740792bcaf0a5c365eb50c4212467aeb3c9569d7658d0

    replay_component17.py
    1e6ef9e322b31593e12483a1e53937bf950f424d8c29433793f40ed98198608a.

For each case P10_001 through P10_012, the adapter cross-checks the
full producer's original-receipt hash against the summary, binds the
saved replay hash, requires PASS and unchanged bound inputs, matches
the case and nonempty internal assignment, source and checker hashes,
root17/cap17/mu41/minimum7, bootstrap0, local43, pinned ordinary
dependencies, model dimensions and the replay's premise fingerprint.
Its exact H, minimum, scale and G must agree with the original
certificate, with G=H-minimum<0 and the recorded gap identical. The
twelve orbit sizes must total291 nonempty assignments in the common
292-assignment,13-orbit catalogue. These are bindings and consistency
checks of already completed exact replays; they do not rerun them.

The producer's premise hash is recomputed unchanged, including its
original P10 dependency registry. A separate replay-evidence hash
includes the stronger exact-replay bindings. The exact68-to-|F|>=68
transfer remains the ordinary root-star/internal-preserving subfamily
argument in `D17-full-model-bridge.md`. P9 cases reject any imported
P10-empty dependency and leave their Y internals free.

The one-case deadline is at most30 seconds, including imports and
reconstruction. The CLI writes only a new receipt under
`degree17_full_replay/` and refuses to overwrite an existing one.
Static AST parsing succeeded. No execution of this prepared replayer
has occurred in this task, and no full D17 exclusion is claimed.

Prepared replayer SHA256:

    3ac2265ad2fd090bf2b06e012ed8c9551f6e7e3bb9d0d7f903fb7d3a756a937b.
