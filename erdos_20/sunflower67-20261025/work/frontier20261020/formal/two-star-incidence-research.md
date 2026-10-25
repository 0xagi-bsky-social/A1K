# Two extremal stars: degree-sensitive incidence and stability

Date: 2026-10-20, America/New_York.

Status: ordinary mathematical derivation and exact arithmetic diagnostic.
These notes are exploratory source material, not an accepted manuscript or a
claim of Lean verification. No new formal module was created for this work.
The root has frozen the assembled A/B and conditional-upper-bound closure.

## Fixed hypotheses and notation

Let F be a finite family of distinct four-element sets with no three distinct
members having identical pairwise intersections. Empty-core sunflowers count.
Let x and y be distinct points of degree twenty, with no member containing both.
Let H be the members omitting x and y, and put m=|H|. The two center stars are
disjoint as families, so |F|=40+m.

Let U and V be the actual supports of the links at x and y. Each has twelve
points; every supported point has link degree five. These are consequences of
the inherited extremal-twenty classification, independent of a chosen canonical
normal form. Neither center lies in U or V.

Put C=U∩V, q=|C|, E=(U\V)∪(V\U). Thus |E|=24−2q.
For v in C, d_H(v)=d_F(v)−10; for v in E,
d_H(v)=d_F(v)−5.

The new proved root
`FrontierTwoStarResidual.residual_meets_link_support_ge_three`
gives |R∩U|≥3 and |R∩V|≥3 for every R in H.
Consequently |R∩C|≥2. This local result does not depend on I(27), an ambient
support bound, the degree bound nineteen, or any finite canonical enumeration.

## General degree bound

Assume d_F(v)≤D for v in U∪V, where D≥10. Double counting gives

    2m ≤ q(D−10),
    6m ≤ 24(D−5)−10q.

The second bound counts incidences in U and V with multiplicity; points in C
are counted twice. Eliminating q gives

    (3D−20)m ≤ 12(D−5)(D−10).

For a fixed integer D, retaining integer q in [0,12] can improve the rational
bound. The exact arithmetic diagnostic in
`two-star-incidence-diagnostics.json` records the attainable bounds in this
relaxed system. For D=18, m≤36; for D=19, m≤40; for D=20, m≤45.
These are upper bounds derived from necessary inequalities, not existence
claims at those endpoints.

## Exact weighted stability identity

Let δ_C=Σ(v∈C)(D−d_F(v)) and δ_E=Σ(v∈E)(D−d_F(v)).
All these deficits are nonnegative under the preceding degree hypothesis.

The two intersection inequalities and four-uniformity permit only the
following row types. Coordinates are the numbers of points in
(C,U\V,V\U,outside U∪V):

    (2,1,1,0);
    (3,1,0,0) or (3,0,1,0);
    (3,0,0,1);
    (4,0,0,0).

Let n_31 count the second type (both orientations), n_30 the third, and n_40
the fourth. Weight each C incidence by 2(D−5) and each E incidence by D−10.
Counting the same weighted incidences by points and by rows gives the exact
identity

    (6D−40)m
      +2(D−5)δ_C +(D−10)δ_E
      +D n_31 +10 n_30 +2D n_40
      =24(D−5)(D−10).

There is no limiting argument or numerical optimization in this identity.
It follows from the stated row partition and the exact residual degrees.

At D=19 this reads

    74m +28δ_C +9δ_E +19n_31 +10n_30 +38n_40 =3024.

The endpoint m=40 forces q=9: q≤8 gives 2m≤72, while q≥10 gives
6m≤236. The common incidence sum then equals

    81−δ_C = 80+n_31+n_30+2n_40.

Thus there are exactly three numerical possibilities:

| Rows of type (2,1,1,0) | n_31 | n_30 | n_40 | δ_C | δ_E |
|---|---:|---:|---:|---:|---:|
| 40 | 0 | 0 | 0 | 1 | 4 |
| 39 | 1 | 0 | 0 | 0 | 5 |
| 39 | 0 | 1 | 0 | 0 | 6 |

This describes necessary equality profiles. It does not construct any of them.

## Removing the noncenter degree-nineteen hypothesis

There is a stronger ordinary derivation using the inherited unconditional
high-point matching theorem

    Erdos20V10HighTriangle.high_point_high_neighbors_le_one

and the unconditional point-degree cap

    Erdos20RankFour.rank_four_degree_le_twenty.

Here two high points are adjacent precisely when a member contains both.

1. Any point v in C is adjacent to both x and y. If v had degree twenty, it
   would have two distinct high neighbors, contrary to the matching theorem.
   Hence d_F(v)≤19 on C, without an additional hypothesis.
2. At most one point of U can have degree twenty, because any such point is a
   high neighbor of x. Likewise at most one point of V can have degree twenty.
   Since no common point is high, E has at most two degree-twenty points.
   All its remaining points have degree at most nineteen.
3. Consequently the incidence bounds become

       2m ≤ 9q,
       6m ≤ 338−10q.

   The allowance of two is only for the two possible high exclusive points.
4. If m≥41, the first inequality forces q≥10; the second then yields
   246≤238, a contradiction.

Therefore the ordinary mathematical consequence is:

**Every four-uniform three-sunflower-free family with two distinct,
noncooccurring degree-twenty points has at most eighty members.**

This conclusion has no I(27) premise and no restriction on the other point
degrees. The needed inherited matching theorem was checked at its literal
source signature; its hypotheses are exactly four-uniformity and
three-sunflower-freeness. The new assembly removing the degree-nineteen
hypothesis has not been written or checked in Lean.

There is additional endpoint rigidity in this stronger setting. If m=40, the
same integer bounds force q=9, and the common-incidence budget remains 81.
Hence all but at most one row have type (2,1,1,0), and there is at most one
point outside U∪V among all residual rows. The whole support therefore has at
most |U∪V|+2+1 =18 points. Any additional high point in E would form a high
edge with x or y, together with the other center as a third high point.
The inherited theorem
`Erdos20V11EdgeThird.high_edge_third_high_support_ge_twenty` then forces
support size at least twenty, a contradiction. A point outside U∪V belongs
to at most one residual row and neither center star, so cannot be high.
Thus an eighty-member endpoint would have exactly the two chosen high
points and would satisfy the three D=19 numerical profiles above.
This endpoint extension also remains an ordinary derivation, not a new Lean root.

## Limits and unresolved stronger directions

The exact independent canonical diagnostics suggest that a nonempty residual
family in fact forces q≥11, and that m≤5. Neither claim follows from the
incidence argument above. A proved minimum-overlap rigidity lemma q≥11 would
already sharpen the degree-nineteen incidence bound to m≤37, but the current
diagnostic is not a theorem and no such lemma is asserted here.

The proposed sharp forty-five result still requires its own complete
normalization, finite-certificate coverage, and semantic bridges. The
incidence result supplies a different, nonenumerative universal nonextension
statement. These notes do not establish global priority or classify all
rank-four sunflower-free extremizers.
