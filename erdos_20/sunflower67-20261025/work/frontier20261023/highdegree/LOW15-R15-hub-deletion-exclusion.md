# A complete R16 link with one hub triple deleted is impossible at cap15

24 October 2026. Ordinary proof development, saved under the existing
Oct23 directory. This argument uses three actual hub anchors and a
literal B4 guard. It does not require a finite trace census, a support
cutoff, a numerical solver, or a neighbourhood upper bound. It is not
a final review, a Lean theorem, or a global67 claim.

## Statement and complete-link geometry

Let F be a finite simple four-uniform family with no three-member
sunflower, including empty core. Assume maximum point degree at most15,
N(Q)>=41 for every actual member Q, and every exact singleton pool at
every actual member has size at most8. Use the universal B4 conclusion
that a singleton pool of size at least8 makes the complementary near
family in that point-link intersecting.

Then no complete point-link in F is R16 with one hub triple deleted.

The cap15 family of size68 has the two numerical hypotheses after H27
and the ordinary no-P9/no-P10 route. The proof below concerns the stated
complete link directly, without assuming a classification of other links.

Suppose x has such a link. Label the four distinct hubs

    K={0,1,2,3}

so the deleted triple is {1,2,3}. All hubs avoid x. R16 has six outer
points partitioned into disjoint triads D,E, each assigned to a pair of
hubs: without loss the pairs are {0,1} and {2,3}. Its outer triples are
the six triples h+e with h in one hub pair and e a two-subset of its
assigned triad, for each of the two triads. The three surviving hub
triples are {0,1,2},{0,1,3},{0,2,3}. All eleven points comprising x,
the four hubs and the two triads are distinct.

The complete x-link has15 triples. Its hub degrees are6 at0 and5 at
each of1,2,3, for a total21. For every satellite hub i in {1,2,3}, let
j,k denote the other two satellite hubs and let D_i be its assigned
outer triad. In the complete i-link, the five triples containing x are
exactly x joined to the edges

    binom(D_i,2) union {{0,j},{0,k}}.                (P5_i)

The triad D_i is disjoint from {0,j,k}. This exact triangle-plus-path
description is the only local link shape used below.

## Residual hub traces and actual anchors

Remove the15 members containing x. On K, let the residual exact trace
counts be s_i for {i}, p_ij for {i,j}, t_i for K minus i, and q for K.
Members disjoint from K and arbitrary exterior identifications are
allowed; no condition on their number or support is imposed. Put

    a=s_0, b_i=s_i for i in {1,2,3}, B=b_1+b_2+b_3,
    X=p01+p02+p03, Y=p12+p13+p23,
    S=a+B, P=X+Y, T=t0+t1+t2+t3,
    E0=S+P+T+q.

All counts are nonnegative integers. E0 counts residual members meeting
K. For i=1,2,3, the member

    Q_i={x} union (K minus i)

is actual. Every x-member meets Q_i. Among the residual members meeting
K, precisely the b_i singleton-i members avoid Q_i. Therefore

    N(Q_i)=15+E0-b_i>=41,
    E0-b_i>=26.                                      (1)

No corresponding anchor Q_0 is assumed actual; it is exactly the
deleted x-cone.

The four global hub degrees sum to at most60, while the x-members
already contribute21. Consequently

    S+2P+3T+4q<=39.                                  (2)

Summing the three inequalities (1) gives

    3E0-B=2S+a+3P+3T+3q>=78.

Subtract this expression from twice the left side of (2). Its upper
bound is78-78=0, and hence

    P+3T+5q<=a.                                     (3)

At Q_j, for distinct satellite hubs i,j, the exact singleton-i pool
consists precisely of residual members with K-trace {i} or {i,j}.
The global singleton bound therefore gives

    b_i+p_ij<=8                     (i,j in {1,2,3}, i!=j).       (4)

Similarly the singleton-0 pool at any Q_j has size a+p0j, so a<=8.
It follows from (3) that

    Y<=P<=8-3T-5q<=8-3t0.                           (5)

Also every b_i<=8. Define the three nonnegative deficits

    delta_i=8-b_i,

and denote their ordered values by delta_min<=delta_mid<=delta_max.

## The neighbourhood lower bound on the satellite triangle

The point0 has six occurrences among the x-members and global degree
at most15. Its residual incidence budget is therefore

    a+X+T-t0+q<=9.                                  (6)

Using the definition of E0, this gives the exact decomposition and bound

    E0=B+Y+t0+(a+X+T-t0+q)<=B+Y+t0+9.

On the other hand (1) gives E0>=26+max_i b_i. Since

    B=24-delta_min-delta_mid-delta_max,
    max_i b_i=8-delta_min,

we obtain

    Y+t0>=1+delta_mid+delta_max.                     (7)

This inequality uses the degree of the special hub0 rather than the
total hub budget. It remains valid for every residual triple trace
and the internal member K if present.

## Literal B4 equality guard for the complete five-star

For distinct satellite hubs i,j let k be the third. We claim

    b_i+p_ij=8  ==>  p_ik+T-t_i+q=0.                (8)

The left side is the exact singleton-i count at the actual anchor Q_j.
Thus B4 makes the near family in the complete i-link intersecting.
Every one of the five known triples containing x is near, since x
lies in Q_j. A near triple avoiding x must therefore meet all five
of these triples; it is a three-point cover of the literal graph
(P5_i).

Such a cover has at least two points in D_i to meet its three triangle
edges. Only one point remains for the two disjoint-from-D_i edges
{0,j},{0,k}, so that point must be their common endpoint0. Hence every
near triple avoiding x is exactly

    {0} union e, with e in binom(D_i,2).             (9)

In particular no such near triple uses j or k or any exterior point
outside D_i. This conclusion concerns arbitrary actual triples; no
enumeration of completions or I7 classification is used.

Every residual member with K-trace {i,k} yields a near i-link triple
containing k and avoiding0, and so is forbidden by (9). Every residual
triple trace containing i yields a near i-link triple containing two
other hubs. If those include0, the other hub is outside D_i; if they
do not, the triple omits0. Either way (9) forbids it. The same is true
of a residual member with K-trace K. Their total count is precisely
p_ik+(T-t_i)+q. All are nonnegative, which proves (8).

The root pairs p0i are not discarded by this guard: (9) permits their
members when their two nonhub points form an edge of D_i. This distinction
is needed for the argument's validity.

## Every satellite pair capacity must be strict

Equation (4) says p_ij<=delta_i and p_ij<=delta_j. We now show that

    p_ij<=delta_i-1 and p_ij<=delta_j-1
    for all distinct satellite hubs i,j.            (10)

First suppose t0>0. For each satellite i, T-t_i>=t0>0. Equality in
either instance of (4) would contradict (8), regardless of whether
the opposite pair category is empty. Since the counts are integers,
all the bounds are strict, proving (10).

Now suppose t0=0. If one satellite pair category were empty, the
remaining positive pair categories would form a path, a single edge,
or the empty graph. In the path case, charge each edge to its endpoint
of degree1; (4) bounds the two edges by the two respective endpoint
deficits, whose sum is at most delta_mid+delta_max. The single-edge
and empty cases satisfy the same bound. Thus an empty category would
imply Y<=delta_mid+delta_max, contrary to (7).

All three satellite pair counts are therefore positive. If equality
held in (4) at i,j, the guard (8) would force the other positive pair
p_ik to be zero. This contradiction again proves the strict integer
bounds (10). These arguments exhaust t0>=0.

## The one-unit contradiction

Sum (10) over the three satellite pairs, using the smaller deficit
at each endpoint. The two pairs incident with a minimum-deficit vertex
are each at most delta_min-1; the third is at most delta_mid-1. Hence

    Y<=2*delta_min+delta_mid-3.                     (11)

Together (7) and (11) give

    1+delta_mid+delta_max-t0
       <=2*delta_min+delta_mid-3,
    delta_max+4-t0<=2*delta_min.

Since delta_max>=delta_min, this implies delta_min>=4-t0. Returning
to (7) and using delta_mid,delta_max>=delta_min now yields

    Y>=1+2*delta_min-t0>=9-3t0.

But (5) gives Y<=8-3t0. This is impossible, and proves the theorem.
No special bound on t0, no omission of the q trace, and no prior
exclusion of residual internal members was needed.

## Consequence for the classified rho7 domain

`LOW15-R15-rho7-classification.md` proves, with its stated universal I7
catalogue import, that a size15 SF3 family with maximum disjoint count
exactly7 is R16 minus one triple. `LOW15-R15-outer-deletion-exclusion.md`
excludes the outer-triple deletion as a complete point-link under the
same numerical hypotheses. The present proof excludes the other type.
Thus a complete degree15 link in the cap15 branch cannot have rho=7.
This conclusion leaves rho<=6 and rho=8 as separate domains; it does
not assume a classification for either of them.

Frozen upstream identities:

| Source | SHA256 |
|---|---|
| LOW15-R15-rho7-classification.md | 151e0cde17bdf12f3ab348248a47d721edadc23baf6aee8e32aeacb0971056e6 |
| LOW15-R15-outer-deletion-exclusion.md | b665f4aa18d202df65383768d9ade1247d4feb46b7beea026e383a7e10180550 |
| LOW15-NO9-fibre-route.md | 576a463ffc3c86138e53d6919f75ead7274a6dd46401a69bc3b6ca8e3b41e0b1 |
| PRIOR_DELTA18_UNLOCK.md | 25b65f695264ae0dbcd5d97b8e66eac421cccbb9970eaf20cc8692886f855b89 |

All other facts used above are proved directly from the stated complete
link, actual-anchor counts, the singleton cap and B4. Earlier source
files and notes were not modified.
