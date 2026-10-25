# Low maximum degree at the 68-member target

23 October 2026. Substantive ordinary research, not final review. The family
F is finite, simple, four-uniform and has no three-member sunflower, including
empty core. Assume |F|=68 and H27, hence every actual member has closed
neighbourhood at least mu=41. When used, crowding26 and the cross-star HP15
theorem are imported in their proved mu>=41, Delta<=18 domain. No old mu42
bootstrap or finite exterior support is assumed.

## New ordinary P10 exclusion at cap 15

**Claim.** Under mu>=41 and global Delta<=15, no point-link contains a P10
subfamily, assuming H27 and the imported cross-star theorem.

Fix ten actual cones x+T, T in P10 on a six-point set Y, and write m=d(x).
Let R contain all members avoiding x. Its exact Y-trace counts, aggregated
by size, are H (singletons), P (pairs), E (triples), I (internal four-sets).
For y in Y write h_y for the singleton count and b_y for the number of
pair-trace members through y. Thus H=sum h_y and B=sum b_y=2P. All these
are counts of actual members; no exterior completion is identified with
another. All Y internals are allowed.

The residual incidence on Y is

    D = H+2P+3E+4I <= 6*15-30 = 60.                 (1)

Thirty incidences are already consumed by the ten prescribed cones.
Other members through x, if any, only strengthen this upper bound. In
particular h_y+b_y<=10, since five prescribed cones use y.

Let W be the sum, over the ten prescribed cones, of the number of residual
members meeting that cone. Every member through x meets every cone, so

    W = sum_T (|N[x+T]|-m) >= 10*(41-m) >= 260.     (2)

A singleton Y-trace meets exactly five P10 blocks; a pair meets exactly
eight. A triple or four-set meets at most ten. Therefore

    W <= 5H+8P+10E+10I,
    3W <= 10D+5H+2B.                              (3)

The latter inequality retains a slack 10I: its right side is
15H+24P+30E+40I. Thus internal members have not been discarded.

The complete singleton pools satisfy H<=27 by H27: any disjoint members
from two different singleton classes would, with a prescribed cone avoiding
those two Y-points, be three disjoint actual members. Their triple tails are
intersecting SF3 and pairwise cross-intersecting. Their distinct centres lie
outside both tail supports. The imported cross-star theorem consequently
gives h_y+h_z<=15 whenever y!=z. It applies with the weaker Delta<=18 guard.

At every y the complete point-link of x inside P10 is a C5. The ordinary
pair/singleton resource table is

    b_y:          0  1  2  3  4  5  6
    h_y at most: 10 10  8  5  4  2  1.             (4)

This table concerns *all* Y-pair traces through y in the C5 case and permits
arbitrary internal members. For completeness, their exterior edges are
pairwise intersecting: a C5 edge avoiding any two distinct partner points
provides the actual sunflower witness if the exterior edges are disjoint.
For equal partners use a cone through that partner. Each singleton tail
meets every exterior edge, and an exterior edge has multiplicity at most two
by triple codegree. The distinct edges form a star or a triangle. A triangle
gives b+h<=6 by charging its three edges. For a star with at least two leaves,
at most two tails avoid the centre and at most 6-b contain it. At b>=5 there
are at least three leaves, so at most one tail avoids the centre. For a
single distinct edge, b<=2 and h+2b<=12 by the two point-pair capacities.
Together with h<=10 these give (4).

Here is a short exact scalar bound, with no LP:

    H<=27, h_i+h_j<=15, h_i+b_i<=10, (4)
       imply 5H+2B<=179.                           (5)

All variables are nonnegative integers. If h<=7, table (4) implies
2h+3b<=20, equivalently

    5h+2b <= (11h+40)/3.

If all six h's are at most seven, summing gives at most
(11*27+6*40)/3=179. Otherwise there is exactly one h>=8 by HP15.

* If it is 10, then b=0 and the other five h's sum to at most 17;
  their score is at most (11*17+5*40)/3=129, giving 50+129=179.
* If it is 9, then b<=1 and the other five h's sum to at most 18;
  their integral score is at most floor(398/3)=132, giving 47+132=179.
* If it is 8, then b<=2. If the other h's sum to at most 18 the bound
  is stronger. If their sum is 19, their score is at most floor(409/3)=136,
  but it is congruent to 19 modulo two, because it has form 5H'+2B'.
  It is therefore at most 135. This gives 44+135=179.

Combining (1)--(5) gives

    780 <= 3W <= 10*60+179 = 779,

a contradiction. This excludes a P10 subfamily in any point-link, without
requiring that it be an entire link component. In particular, at cap15
every exact singleton has size at most nine. This is a new usable
mu41 conclusion; it is not a transfer of the old r10>=7 bootstrap.

## A related P9 bound, and the cap14 consequence

Prescribe nine cones x+T from P9=P10 minus a block A on Y, and put C=Y\A.
Let H_A,H_C be the whole singleton-pool sums on these two three-point sets,
and let P_CC count residual pair traces wholly in C. Keep D,H,P,E,I as above.
There are 27 prescribed incidences; points in A occur four times, points
in C five times. For a global cap Delta=d,

    D<=6d-27,
    h_y+b_y<=d-4 (y in A),
    h_y+b_y<=d-5 (y in C).

Each singleton in A meets four cones, each in C five; pairs in C meet eight,
other pairs seven; every triple/four-set meets at most nine. Hence

    W >= 9*(41-m),
    W <= 3D + H_A+2H_C+P+P_CC.

Write B_A=sum_{y in A}b_y and B_C=sum_{y in C}b_y. Since
P+P_CC<=B_A/2+B_C, the last extra term is at most

    sum_A (h_y+b_y/2) + sum_C (2h_y+b_y)
      <= (3/2)(d-4)+3(d-5)+(H_A+2H_C)/2.

P9 still has a block avoiding each pair of Y-points. Thus H_A+H_C<=27
by H27, and the three HP15 inequalities inside C give 2H_C<=45, hence
H_C<=22. Consequently

    9*(41-m) <= W <= (45d-155)/2.                 (6)

At d=14 and m<=14, (6) would require 243<=475/2, impossible. Thus under
cap14 **no point-link contains P9**, and every exact singleton has size
at most eight. At cap15 the same bound only says that a point whose link
contains P9 must have degree at least 13; it does not exclude P9.

This argument also permits arbitrary Y internals and arbitrary exterior
support. It uses the C5/P5 occurrence counts only to count prescribed cone
incidences, and does not apply the C5 pair table to a P5 point.

## What can already be excluded globally

Crowding26 implies the sum S of four exact singleton counts at an actual
anchor is at most 34. With P the pair sum and T the triple sum at that
anchor, its degree sum D_R and neighbourhood N satisfy

    N=1+S+P+T,
    D_R=4+S+2P+3T=2N+2-S+T >=2N-32.

If Delta<=13, then D_R<=52, hence N<=42 at every anchor. The disjointness
graph G of the 68 members is triangle-free, has independence number at most
27 by H27, and minimum degree at least 26. The already imported Jin theorem
with k=3 applies since 26*11>4*68. It gives a homomorphism to the Wagner graph
on eight vertices. Let a_i be fibre sizes and
b_i=a_{i-1}+a_{i+1}+a_{i+4}<=27. With e_i=27-b_i, the elementary Wagner
incidence identity gives

    sum e_i=216-3*68=12,
    a_i=81-68-e_{i-1}-e_i-e_{i+1}>=1.

Every fibre is occupied. Its vertices need at least 26 neighbours, so b_i>=26.
But 8*26<=sum b_i=3*68=204 is impossible. Therefore Delta>=14, conditional
on H27, crowding26 and the imported graph theorem. This argument is ordinary;
Jin itself is an external theorem, not re-proved here.

The new cap14 singleton bound improves its local neighbourhood estimate:
S<=32 gives D_R>=2N-30, and D_R<=56 yields N<=43. This is useful but does
not yet exclude cap14 at 68. The remaining cap15 branch has singleton<=9,
but the preceding argument has not established a global N<=43 bound there.

There is a sharper ordinary description of the surviving cap14 domain.
Every anchor has D_R>=52. Any point y in such an anchor has
d(y)+3*14>=52, so every used degree is at least ten. Writing its four
degree deficits as e_i=14-d_i gives e_i>=0 and sum e_i<=4. Convexity of
1/(14-e), or moving all deficit to one coordinate, gives

    sum_{y in R} 1/d(y) <= 1/10+3/14 = 11/35.

Summing over the 68 members counts each support point exactly once. Thus
the support has at most floor(68*11/35)=21 points, and incidence counting
gives at least ceil(272/14)=20. A surviving cap14 family therefore has
**20 or 21 used points, degrees 10 through 14, and all neighbourhoods 41
through 43**. Further, for a co-occurring pair u,v, the two opposite singleton
classes are now at most eight, so

    41 <= d(u)+d(v)-d(u,v)+8+8+3,
    d(u)+d(v)>=22+d(u,v)>=23.

These are derived support and degree restrictions, not an assumed finite
support model. They still do not prove that this last domain is empty.

## Why the previous LOW15 and degree16 routes do not close this target

The frozen LOW15 generators use mu=42, r9=r10=7 and minimum used degree four.
Their 28 high-anchor orbits, 35 cores and final 33-equality certificate cover
that domain. Replacing minimum four by the available minimum seven does
not justify deleting the r9/r10 premise or adding mu41 rows. No old census
or certificate was run or transferred here.

Even if its local N<=43 conclusion were separately recovered at cardinality
68, the old graph contradiction would fail. Then minimum graph degree is
25, and Jin still gives A3 since 25*11>4*68. The average allowed degree is
3*68/8=25.5, compatible with minimum 25. For example a complete Wagner
blow-up with fibre sizes (8,8,8,8,9,9,9,9) has 68 vertices, minimum degree
25 and independence number 26. It is only a graph, not an SF4 family, but
it disproves this proposed graph-only contradiction.

Thus excluding degrees 17 and higher would only give Delta<=16; an additional
LOW15 exclusion is still required to assert the existence of a degree16
point. Moreover, existence of such a point does not force an R16 link.
The prior NO9 and NO45 reductions provide singleton<=8 and N<=44 at size69
under their mu42 domains. They are not inherited at size68. Their *roles*
remain necessary for that particular fibre route unless replaced by other
arguments: a valid neighbourhood bound supplies the graph minimum degree,
and singleton/transversal control excludes the other complete link types.
Indeed at size68, N<=44 gives minimum degree24, whereas the old fibre census
was explicitly at size69 and minimum degree25. Merely recovering the old
two numerical conclusions would still require a new graph/fibre bridge.

The existing R61 theorem does transfer once a complete R16 link is actually
forced: it already assumes only mu>=41 and Delta<=18. It does not create
such a link or establish maximum degree16.

## Source and computation boundary

Ordinary source foundations are the frozen Oct20 prior-art68 repository:
`paper/main.tex` crowding/cross-star and R61 sections;
`companion/upstream/D17/UNIVERSAL_EXTENSION_LEMMAS.md` for the pair resource
table and complete singleton pools; and `companion/upstream/LOW15/PROOF.md`
plus `CURRENT_PREMISES.md` and its two generators for the old domain.
The exact mu41/minimum7 bridge is reconstructed in
`prior-art68/analysis/mu41/mu41-analysis.md`; its successful selected replays
are already recorded in the Oct20 ledger and receipts. The current
`PRIOR_DELTA18_UNLOCK.md` records the source-bound reuse.

Only tiny standard-library arithmetic enumerations were used as discovery
checks here: sorted four-degree tuples, and six integers h in [0,10] with
the table bounds. The scalar179 result is proved above without relying on
that enumeration. No LP, heavy replay, Lean job, or global exclusion of 68
has been performed or claimed.
