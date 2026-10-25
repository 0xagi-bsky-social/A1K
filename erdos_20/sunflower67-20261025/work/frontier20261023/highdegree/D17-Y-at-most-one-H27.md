# The whole residual zero-or-one-Y family is intersecting

23 October 2026. Ordinary model-development lemma for the D17 projection.
No model, solver, or replay was executed while preparing this addition.

## Literal premises and proof

Let x be the distinguished root and let H be the prescribed P9 or P10
subfamily of its complete triple link, supported on the six-point set Y.
All root cones {x} union T, T in H, are actual members of the same SF4
family F. The remaining members of F avoid x; call them residuals.

The collection

    C={Q in F: x not in Q and |Q intersect Y|<=1}

is intersecting on arbitrary support. Indeed, if Q,Q' in C were disjoint,
their combined Y trace would have size at most2. A prescribed H block T
avoids this trace. Then Q,Q' and {x} union T would be three distinct
pairwise disjoint actual members, an empty-core sunflower.

For completeness, every pair of Y points is avoided by two P10 blocks:
each point lies in five of its ten blocks and each pair in two, so
the number meeting the pair is5+5-2=8. Deleting one block to form P9
leaves at least one avoiding block. Traces of size0 or1 are covered
by extending them to a two-point subset of Y.

Since C is an intersecting SF4 subfamily, H27 gives the unconditional row

    sum_(residual trace s: popcount(s intersect Y)<=1) n_s <=27.

There is no cutoff on the unrepresented exterior support or on the size
of the full core. Every residual member has exactly one represented
trace and hence is counted once. In particular the row includes empty
Y traces, proper traces, and full four-point traces, with arbitrary
allowed multiplicity. The proof uses a fixed actual avoiding cone for
each pair of possible trace classes; it is also a literal H27 trace clique.

No root-cone offset is subtracted: C consists only of root-avoiding
residuals. The other root cones, including the whole opposite link
component, are not asserted to belong to this intersecting subfamily.

## Why this changes the current projection

The frozen v5 source has `Y-pool-H27`, which counts only exact-one-Y
residuals, and `small-complete-core-intersecting-H27`, which counts
residuals with at most two points in the entire Y-plus-Z core. Neither
is the displayed whole zero-or-one-Y row. A transferred external H27
clique file can already contain it for an individual run, but it is
not an unconditional built-in row in v1--v5.

The new `degree17_full_projection_v6.py` copies v5 and adds exactly
this unconditional row, labelled `Y-at-most-one-H27`, alongside the
existing Y-pool row. The ordinary note and v5 adaptation source are
included in the receipt's source-hash-bound dependency set, and the
literal premise list states the root-avoiding family explicitly.
The model interface and extra-actual-member handling are unchanged.

The proposed conditional pair-row improvement was checked against
the existing local source. `local43.py` already has `if s>=8: if r>6
or k>10: continue` in `local_s_candidates`, which the central catalogue
calls for all four local roots. That filter is not duplicated here.
The cross-root triple-star bounds would need a separate joint-state
comparison before being advertised as an additional strengthening;
they are not part of this v6 change.

## Saved-primal discovery diagnostic

Read-only arithmetic on the four saved P9-Q8 stage1 primal trace lists
gives the following values for the new row. These are fractional saved
solutions, not actual families or exact infeasibility certificates.

| Case | Zero-Y mass | One-Y mass | Combined mass | Excess over27 |
|---|---:|---:|---:|---:|
| IZ00 | 13.340476190476 | 25.072222222222 | 38.412698412698 | 11.412698412698 |
| IZ02 | 13.517647058824 | 24.776470588235 | 38.294117647059 | 11.294117647059 |
| IZ04 | 13.659090909091 | 23.488636363636 | 37.147727272727 | 10.147727272727 |
| IZ06 | 13.705882352941 | 23.500000000000 | 37.205882352941 | 10.205882352941 |

Thus the row removes each saved optimum. Whether the strengthened
relaxations exclude their branches requires newly scheduled runs and
exact receipt checks. No such closure is claimed by this note.
