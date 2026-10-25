# The remaining cap15 high cores after NO9

23 October 2026. Ordinary proof development, with arbitrary exterior
support. No solver, new census, or Lean compilation was run for this note.
All earlier notes and producers remain unchanged. The result below reduces
N44 to four arithmetic profiles; it does not exclude N44 or cap15.

## Premises and the usable local lemma

Let F be a finite simple sunflower-free four-uniform family of size68,
including the prohibition on empty-core sunflowers, with maximum point
degree15. Use H27, B4, I8 classification/isolation and HP15 in their
recorded mu>=41, Delta<=18 domain. The acyclic ordinary argument in
`LOW15-two-low-core.md` gives N(Q)<=44 for every actual Q; the subsequent
`LOW15-NO9-fibre-route.md` excludes P9 from every point-link and therefore
gives exact singleton counts at most8 at every actual anchor.

At an actual R={0,1,2,3}, write s_i for exact singletons, p_ij for exact
pairs, t_i for the exact triple omitting i, and r_i=sum_j p_ij. Put
S=sum s_i, P=sum p_ij, T=sum t_i. Thus

    N=1+S+P+T,
    d(i)=1+s_i+r_i+T-t_i,
    sum_i d(i)=2N+2-S+T.

Universal bounds are p_ij<=3, t_i<=1, global triple codegree<=2.
Call i good when s_i=8 and r_i>=5. The ordinary proof in
`LOW15-large-singleton-core.md` establishes the following facts, also
when T is positive:

* If s_i=8, then r_i<=6.
* At a good i, every incident pair residue lies on one exterior triangle
  A_i. Each edge occurs in at most two categories. The entire far family
  D_i avoids R union A_i, including both possible Q8 leaves.
* If two good roots share a category of size at least2, their triangles
  agree. At a good root of category sizes (3,1,1), the two singleton
  exterior edges are distinct; two distinct shared edges also identify
  the triangles.
* Three good roots with one common triangle A are already contradictory
  if the remaining root has a positive pair category to one of them.
  A member of that category avoids the other two good roots and their
  far supports. It forces their two size8 far families to be
  cross-intersecting, contrary to HP15. No isolation at the fourth root
  is needed.
* If t_l=1 and every other root has singleton8, then r_l<=4. This is
  the literal triple-member/bipartite-graph argument, not a support bound.

One additional useful consequence is immediate. Suppose t_l=1, l is
good, r_l=6, and at most one other root has singleton below8. Write its
triple member as (R minus l) union {z}. B4 at each other singleton8 root
makes all pair residues from l to that root contain z. At least one such
category is positive because a single category has size at most3.
Consequently z lies on A_l. All three edges of A_l occur twice, since
r_l=6. The edge avoiding z can occur only in the one remaining partner
category, where edges are distinct, so it occurs at most once. This is
a contradiction. This argument does not apply B4 at a singleton7 root.

## N44 with at least three singleton8 roots

The degree identity gives S>=30+T, while S<=32. The only sorted singleton
patterns are (6,8,8,8), (7,7,8,8), (7,8,8,8), (8,8,8,8).

First take (8,8,8,8). If T=1, the omitted row is at most4 and the other
three rows at most5 by the degree cap. Their sum is at most19, but
2P=2(43-32-1)=20. If T=2, omitted rows are at most4 by the same lemma,
and non-omitted rows are at most4 by the degree cap; this contradicts
2P=18. Larger T is ruled out by S>=30+T.

For T=0 the four rows sum to22 and each is at most6. Their multiset is
(5,5,6,6) or (4,6,6,6). The first is excluded by the common-triangle
theorem. In the second, the three row6 roots have total internal pair
count (18-4)/2=7. Their graph of categories of size at least2 is
connected: a disconnected graph on three vertices has at most one such
edge, and its pair-count sum is at most3+1+1=5. Their triangles agree;
the positive row4 supplies the complementary-pool witness described
above. Thus this pattern is impossible.

Next take (7,8,8,8). Here T<=1. If T=1 all four degrees are15. If its
omitted root is the singleton7 root, its row is7, contradicting the
omitted-row bound4. Otherwise the omitted root has singleton8 and row6,
and the additional triangle-edge argument above applies. Thus T=0.

The rows now sum to24. Their possibilities are a singleton7 row6 with
three good rows6, or a singleton7 row7 with good rows5,6,6. In the first
case the internal pair sum on the three good roots is6, so their
triangle-identifying graph is connected. In the second case its sum is5.
If connected, the same witness applies. If disconnected, the three
pair counts must be (3,1,1). The isolated vertex has row at most5, so it
is the row5 root; its category to the singleton7 root has size3. Its
two singleton edges, towards the already identified row6 roots, are
distinct by triple codegree2. They identify its triangle with theirs.
The singleton7 root again has a positive category to a good root, giving
the same HP15 contradiction. This pattern is impossible.

Finally take (6,8,8,8). Necessarily T=0, all degrees are15, and the pair
rows are8,6,6,6. The internal pair sum on the three good roots is5. If
their identifying graph were disconnected, its counts would be (3,1,1);
the isolated row6 root would then require a category of size4 to the
singleton6 root, impossible. Their triangles are therefore common.
Every pair residue incident with the singleton6 root is on that common
triangle. Its eight occurrences exceed the capacity of two per edge.
This excludes the pattern without assuming isolation at that root.

## Four remaining arithmetic N44 profiles

Only sorted singletons (7,7,8,8) remain. Label the singleton7 roots0,1
and the singleton8 roots2,3. Then T=0, every degree is15, and the rows
are (7,7,6,6). Put a=p01, b=p23. Subtracting the two low-root row sums
from the two high-root row sums gives a=b+1. Hence b is0,1,2. The cross
counts satisfy

    p02=p13=u, p03=p12=v, u+v=6-b.

After swapping roots within the two pairs, take u<=v. In pair order
(01,02,03,12,13,23), the complete list is

| b | p |
|---|---|
|0|(1,3,3,3,3,0)|
|1|(2,2,3,3,2,1)|
|2|(3,1,3,3,1,2)|
|2|(3,2,2,2,2,2)|

This is an algebraic list, not a count of exterior geometric cores.
Roots2,3 are good. For b=2 their triangles agree; for b=1 a single
shared edge does not identify triangles. In none of these cases may
one silently make the singleton7 roots' near links intersecting.
Their near links have size8, but B4 is a statement about the size of
the opposite far family, which here is only7.

## Why the same proof does not close N43

For N43 the degree identity only gives S>=28+T. More profiles are possible.
Even the all-singleton8, T=0 subcase has an actual remaining obstruction
to the present proof. Its row sum is20 and each row is at most6. Four
good roots are excluded by the common-triangle theorem. With precisely
three good roots and remaining row q, one has 2<=q<=4, and their internal
pair sum is10-q>=6. They have one triangle and the positive q row again
gives the HP15 witness.

With only two good roots, however, the rows can be (4,4,6,6). Their
shared category has size at least2, since p_HH-p_LL=2, so their triangles
agree. A row4 singleton8 root may be Q8: isolation removes its five-point
core, but not automatically its leaves. At a triangle point its near
bipartite graph can have only two edges sharing a partner, and the
matching-of-size2 proof used above is unavailable. Thus this note does
not assert that all four far supports avoid the common triangle.
The cap14 proof had all rows5 and does not cover this case unchanged.

Excluding N44 alone would leave N<=43, hence minimum disjointness degree25
on68 vertices. The Wagner/Andrasfai fibre problem is still feasible at
that numerical level. To copy the final contradiction in
`LOW14-NO43-ordinary-closure.md`, one needs N<=42, not merely N<=43.

## Source-only complete-core continuation

`LOW15_mu41_complete_core.py` is a new, solver-free preparation inspired
by the prior `LOW15/scripts/primary.py`. It changes the domain to mu41,
cap15, singleton<=8, N<=44, and no bootstrap r9/r10 restrictions. It
builds one shared trace system for every actual member of the complete
root core C(R)={Q in F: |Q intersect R|>=2}; fresh exterior labels are
introduced at every category attachment. This is a finite normalization
of the prescribed core, not a bound on the support of F. The empty trace
and exact family cardinality68 are retained. Every additional family
member has a trace meeting R in at most one point, with arbitrary
exterior multiplicity.

The new source is prepared only. No rows, cores, or models were generated
and no feasibility conclusion is attached to it. Its local-row import is
the universal `local43.py`, SHA256
`258221ffe8594e51616bdd125109d92151bfea13557f4e385ef453ab2e03152b`.
The old primary source, SHA256
`702ddf28268ff54b009fbe4dd17172f849a531d726f97934204faaf889d3450c`,
is provenance only; its mu42 and bootstrap domain are not reused.

### Exact family-to-model map of the prepared source

Take any actual high anchor R in a family satisfying the stated premises.
The pinned universal local43 domain is called with mu=41, cap_degree=15,
r9=r10=0, then filtered only by singleton<=8 and N<=44. It initially
orders the four degrees; all24 root relabellings restore every ordering.
No minimum used-point degree is imported. The local43 cost and equality
guards remain their stated universal necessary conditions; this is not a
claim that every admitted row has a realization.

Each nonempty exact pair category consists of an intersecting graph of
one, two, or three exterior edges: respectively an edge, a two-edge path,
or a triangle. The last statement uses triple codegree2 to exclude a
three-edge star. Each exact triple category supplies one exterior point.
Attaching these categories by all injections into previously used points
and fresh points realizes every possible identification. Ordering fresh
labels by first appearance removes labels, not cases. The source keeps
possibly isomorphic cores rather than relying on a difficult canonical
label calculation. Its two incremental rejection rules are literal
sunflowers and pairs of near triples with empty intersection in a
singleton8 root's link, excluded by B4. A node-limit exception reports
incompleteness and never produces an exhausted-census certificate.

Let V be the support of the resulting complete core C. For every subset
U of V of size at most4 with |U intersect R|<=1, assign z_U equal to the
number of members in F minus C whose exact trace on V is U. This includes
U empty and permits every identification outside V. Traces meeting R
twice are absent by the definition of C, not a support assumption. A
trace is removed if two fixed core members and any member with that
trace would be a sunflower; their pairwise intersections are determined
entirely inside V, so this deletion is valid for arbitrary exterior tails.

For nonempty U, its box upper bound is the global codegree cap for U
minus the number of fixed core members containing U: 15,6,2,1 for sizes
1,2,3,4. This bounds the exact trace count by the remaining inclusive
codegree. The empty trace lies in D(R), which is intersecting because
R is actual; H27 gives its upper bound27. The mass row is exactly
sum_U z_U=68-|C|. The separately recorded disjoint-root row is
sum_(U intersect R empty) z_U=68-N(R); it is redundant with mass and
the root's trace equations, but has the same actual-family meaning.

For every actual Q in C, choose its actual universal local row. Its
proper nonempty trace counts are the fixed counts from C plus the same
z_U summed according to U intersect Q. These are the14 exact equations
for six pairs, four omitted-point triples, and four singletons. The
selector normalization chooses one row; allowing fractional selectors
only weakens the system. Rows are removed only when their trace counts
lie outside the fixed-count/box intervals, their point degrees disagree
with the original root's actual degrees, their degrees fall below the
fixed incidences, or a displayed pair of disjoint near triples contradicts
B4 at a proposed singleton8 position. At Q=R the chosen row is exactly
the supplied root row. If no row remains, the normalization is 0=1,
an explicit necessary-system contradiction rather than a missing case.

Finally, the inclusive point/pair/triple incidence rows on V subtract
all fixed core occurrences from their global caps. These use the same
trace variables as every anchor equation. Thus every actual family gives
an integral feasible point of the emitted system. An eventual exact
infeasibility certificate could exclude that particular complete core;
global exclusion would additionally require exhaustion of all arithmetic
rows and every core identification, with all dependency hashes checked.
None of those future computational conclusions is asserted here.
