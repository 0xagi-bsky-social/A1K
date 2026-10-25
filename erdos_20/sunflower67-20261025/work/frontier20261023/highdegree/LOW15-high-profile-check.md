# Cap15 high-anchor arithmetic and triangle reductions

23 October 2026. Ordinary proof development with a small standard-library
integer census. This is not an exterior-core census, LP, final audit or
global exclusion of a 68-member family. A surviving arithmetic row need
not have any geometric realization.

Assume a simple SF4 family of68 members, global point cap15, H27 and the
imported crowding26/B4 facts. Thus mu>=41. The ordinary P10 cone-average
argument in `LOW15-mu41-research.md`, independently checked in
`LOW15-count-check.md`, gives exact singleton cap9. We use neither the old
mu42 bootstrap nor a bound on the number of exterior points.

## Complete arithmetic domain

For an actual root R={0,1,2,3}, p_ij denotes its exact pair count, t_i the
exact triple count omitting i, and s_i its exact singleton count. Put
P=sum p, T=sum t, S=sum s and r_i=sum_(j!=i) p_ij. Then

    N=1+S+P+T,
    k_i=1+r_i+T-t_i,
    d_i=s_i+k_i,
    sum d_i=2N+2-S+T.

The exact trace caps are p<=3,t<=1,s<=9, and the three largest s sum to
at most26. Hence S<=34 and N<=46. If N>=45, S>=32+T and T<=2. The only
sorted singleton vectors are

    (6,8,9,9), (7,7,9,9), (7,8,8,9), (8,8,8,8),
    (7,8,9,9), (8,8,8,9), (8,8,9,9).

For N46, equality forces S34,T0, all degrees15 and s=(8,8,9,9).
For N45, the complete arithmetic domain is obtained by these seven s,
all six p in0..3, all four t in0..1, the displayed exact identities,
d_i<=15, and the global pair-codegree inequalities

    1+p_ij+sum_(h outside {i,j}) t_h <=6.

`LOW15_high_profile_census.py` enumerates precisely this bounded domain,
then acts on p,t,s together by all24 root permutations. The t indices
are omitted vertices, so they transform with the same root permutation.
Sorted s loses no orbit because every actual row can be renamed to
have sorted singleton counts. Each full oriented orbit size is recorded.

## Two additional B4 arithmetic exclusions

If t_l=1, its actual member is (R minus l) union {z}. At any j!=l with
s_j>=8, B4 makes the near j-link intersecting. A pair-category lj member
must therefore have z in its exterior edge. In particular p_lj cannot
equal3: its three exterior edges would be a triangle, with no common
point. This is the first rejection flag in the census.

If all three j!=l have s_j>=8, every edge in all categories lj uses z.
After removing l,z, their actual members give a simple bipartite graph
between R minus l and the other exterior points. Its maximum degree is
at most2 by triple codegree. It has no three-edge matching, since that
would lift to a sunflower with core {l,z}. A bipartite graph of maximum
degree2 consists of paths and even cycles; every component has at most
twice as many edges as its matching number. Thus r_l<=4. This is the
second rejection flag. It uses arbitrary exterior points, not a cutoff.

The count after these two necessary cuts is:

| N | Initial S4 orbits | Initial oriented rows | Orbits after B4 cuts | Oriented rows after cuts |
|---|---:|---:|---:|---:|
|45|138|2620|76|1330|
|46|5|54|5|54|

The N45 profile breakdown (initial / after the two cuts) is:

| Sorted s | T | Orbits |
|---|---:|---:|
|(6,8,9,9)|0|2 / 2|
|(7,7,9,9)|0|3 / 3|
|(7,8,8,9)|0|4 / 4|
|(7,8,9,9)|0|14 / 14|
|(7,8,9,9)|1|15 / 8|
|(8,8,8,8)|0|3 / 3|
|(8,8,8,9)|0|7 / 7|
|(8,8,8,9)|1|8 / 0|
|(8,8,9,9)|0|27 / 27|
|(8,8,9,9)|1|36 / 4|
|(8,8,9,9)|2|19 / 4|

## Which rows force a common exterior triangle

Call i good when s_i>=8 and r_i>=5. B4 makes all incident exterior edges
pairwise intersecting. If an incident category has size3, it is a triangle,
and every other edge must cover that triangle, hence be one of its edges.
Otherwise all three category sizes are at most2 and sum at least5, so their
sizes are (2,2,1) or (2,2,2). An intersecting edge union is a star or triangle.
A star with at least three distinct edges admits distinct representatives
from the three categories and makes a sunflower. A star with at most two
edges repeats an edge three times and violates triple codegree2. Thus all
incident edges lie on a unique triangle.

Two good vertices sharing a category of size2 or3 have the same triangle:
two distinct edges determine its three vertices. A further safe propagation
rule handles a good vertex of category sizes (3,1,1). Its two singleton
edges are distinct, because their equality would repeat one edge in all
three categories. If the other endpoints of those two categories already
have the same triangle, its triangle agrees with theirs as well.

The census implements these sufficient propagation rules and checks that
every positive pair category is incident to a good vertex. Whenever all
good triangles are then identified, all pair edges lie on one triangle.
Triple codegree2 bounds every root pair-row by6, including rows at points
where B4 was unavailable. This gives an immediate contradiction if any
row exceeds6. Exactly10 of the76 surviving N45 orbits meet this test:

    071,072,073,085,118,119,120,128,139,140

with the prefix CAP15_HIGH_. They represent180 oriented rows. This removes
both (6,8,9,9) orbits, all four (7,8,8,9) orbits and four (7,8,9,9) orbits.
It is a sufficient ordinary deduction, not an assertion that these are all
possible ways to force a common triangle.

If all four singleton counts are at least8, T=0 and all four pair-rows are
at least5, the common-triangle argument applies to the whole core. Heavy
categories connect the good triangles. If their graph is disconnected,
it consists of two edges, and the distinct singleton-edge argument joins
the two components. Each triangle-edge multiplicity at a root is at most2,
so a row of size5 or6 has multiplicities (2,2,1) or (2,2,2). Every exterior
triangle vertex has a two-edge matching in that root's near point-link.

The P8/Q8/P9 isolation argument, with the Q8-leaf matching step checked in
`NO43-Q8-leaf-check.md`, puts all far singleton tails outside the core.
An opposite pair member then makes two actual singleton pools of sizes at
least8 cross-intersecting, contradicting HP15. This closes all5 N46 orbits
and15 further N45 orbits (190 oriented rows). The latter are disjoint from
the10 row-capacity contradictions.

After these stated deductions,51 N45 arithmetic orbits (960 oriented rows)
remain. Their counts by (sorted s,T) are:

    (7,7,9,9;0):3;   (7,8,9,9;0):10; (7,8,9,9;1):8;
    (8,8,8,9;0):2;   (8,8,9,9;0):20;
    (8,8,9,9;1):4;   (8,8,9,9;2):4.

These are the next arithmetic boundary, not51 actual geometric cores.
The two-low-singleton rows and rows with a pair-row below5 are natural
places where a new literal argument is needed.

## A complete-link complement cut for actual triple traces

One further safe deduction reduces the above51 to37 N45 arithmetic orbits
(708 oriented rows). Suppose t_l=1,s_l=9 and there is j!=l with s_j>=8 and
p_lj>0. Write the actual triple-trace member as Q_l=(R minus l) union {z}.
B4 at j forces z to lie in every exterior edge of category lj. Thus some
actual near triple in the l-link uses z.

The exact singleton tails at l form P9, on a six-point support W disjoint
from R. P9 isolation puts every near triple outside W: the only exceptional
triple is its missing P10 block, which is entirely on W and hence could
not be near R minus l. Therefore z lies outside W, so Q_l avoids all nine
singleton cones through l.

Every other member through l has another root point and consequently meets
Q_l. Hence the complete l-link inside D(Q_l) is exactly this P9. Moreover,
D(Q_l) is intersecting, since two disjoint members together with Q_l would
be an empty-core sunflower. The ordinary complete-link bound20 from the
frozen paper applies with both guards proved. Since every actual anchor
has N<=46 already from arithmetic,

    68=|N[Q_l]|+|D(Q_l)| <=46+20=66,

a contradiction. This uses no general claim that a contained P9 must be
a complete link. The census records the literal (l,j) witness for this
special implication.

It closes14 orbits (252 oriented rows) among the16 surviving T>0 orbits.
The only T>0 cases left are CAP15_HIGH_054 and CAP15_HIGH_101:

    p=(0,2,2,2,2,2) or (1,1,2,2,1,3),
    s=(9,9,7,8), t=(0,0,0,1), d=(15,15,15,15).

Both omit the singleton8 point, so the P9 complete-link bound does not
apply there. Their exact displayed degree vector is recomputed by the
code from p,t,s; no degree ordering is part of canonicalization.

These last two triple-trace rows have a separate contradiction. At l=3,
the pair-row has size6 and B4 puts its exterior edges on one triangle.
B4 at0,1 forces every E30 and E31 edge to contain the external point z of
Q_3. Since these categories are nonempty, z is a vertex of that triangle.
The two triangle edges at z each have multiplicity at most2, for a total
capacity4. In row054, E30 and E31 contribute2+2 occurrences at z, while the
two-edge E32 category contributes at least one more. In row101, they
contribute2+1 and the three-edge E32 triangle contributes two. Both demand
at least5 occurrences, a contradiction.

More generally, if t_l=1,s_l>=8,r_l>=5 and at least one high-singleton
neighbour j has p_lj>0, the triangle argument yields the necessary cut

    sum_(j:s_j>=8) p_lj + sum_(j:s_j<8) max(p_lj-1,0) <=4.

The first categories must use z; any other category of p distinct triangle
edges has at least p-1 edges through z. This cut is separately flagged.
It removes precisely the last two T1 orbits (36 oriented rows), leaving
**35 N45 arithmetic orbits, all T0, representing672 oriented rows**. Every
N46 orbit and every N45 orbit with a positive triple trace is excluded by
the ordinary implications recorded here. Geometric realizability of the
35 remaining arithmetic orbits is open in this note.

## Further ordinary reduction supplied by the large-singleton note

I independently checked the final T0 section of the subsequently saved
`LOW15-large-singleton-core.md`. It excludes all N45 rows having every
singleton at least8. With three pair-rows at least5, the pair counts among
those three roots sum to at least6, so their categories of size at least2
connect their triangles. A positive pair category incident with the fourth
root then witnesses cross-intersection of the other two large pools. With
only two such rows, they are6,6 at singleton8 points, while the other two
rows are4,4 at singleton9 points. The identity p_HH-p_LL=2 identifies the
two large triangles; each singleton9 point sees a size-two category into
that triangle, so P9 isolation suffices there without a near matching.

These arguments preserve all actual-centre guards of HP15 and exclude the
22 all-large rows remaining at the preceding checkpoint. The ordinary
boundary is therefore **13 T0 arithmetic orbits**: three with sorted
singletons (7,7,9,9), and ten with (7,8,9,9). This is a later mathematical
deduction, not an alteration of the frozen census flags or hashes above.
The next work concerns their actual geometric cores.

## Exact-link guard for the proposed shortcut

The frozen paper at lines1121--1144 proves that an intersecting SF4 family
with a **complete** P9 or P10 point-link has at most20 members, including
internal four-sets. A contained P9/P10 star is insufficient to invoke that
statement. The complement D(Q) of an actual member is intersecting as
four-sets; its x-link need not be intersecting, since all x-cones already
meet at x. Isolation permits additional x-link triples outside the P9/P10
support. Those may also avoid Q. Therefore absence of P10 does not by itself
make a contained P9 the complete link in D(Q). No such shortcut was used
in this census or in the exclusions above.

## Unconditional B4 pair-row cap and a cap16 consequence

For every actual root, s_i>=8 implies r_i<=6, regardless of T. If every
pair category has size at most2 this is immediate. Otherwise the category
of size3 is an exterior triangle. B4 forces every other incident exterior
edge onto that triangle, and triple-codegree2 bounds each of its three
edge multiplicities by2. Extra triple-trace members cannot invalidate any
of these necessary constraints. At cap15 this cut follows already from
d_i=s_i+1+r_i+T-t_i<=15, but at larger caps it is an additional restriction.

For example, at global cap16 crowding26 gives S<=34 and therefore N<=48.
Equality N48 forces all degrees16, S34,T0. With the universal singleton
cap10, the possibilities are (8,8,8,10) and (8,8,9,9). Their pair-rows
are respectively (7,7,7,5) and (7,7,6,6). Both violate the unconditional
B4 row cap at a singleton8 point. Thus N<=47 at cap16, independently of
any attempted contained-P9/P10 complement shortcut.

## Source and computation record

The source is the frozen prior-art68 `paper/main.tex`: lines188--331 for
canonical intersecting families, isolation and B4; lines333--372 for
universal caps and exact traces; lines968--1024 for crowding/cross-star.
The new singleton9 bound is in `LOW15-mu41-research.md`, with the independent
scalar and count check in `LOW15-count-check.md`. These dependencies remain
ordinary/imported results; the complete chain is not Lean-formalized here.

The census ran using Python's standard library, with no numerical model
import or solver. Source SHA256:
`bf5fe9e36909c5ad4f732b2490c613d93c9d69e409c48004cf897e6586c10c7d`.
Output `LOW15-high-profile-census.json` SHA256:
`8d4bebfd94168829f559ad083dfbf15f8e6e18456bc43754e01d477e8ec4d114`.
The output contains every canonical row, orbit size, literal arithmetic
rejection, and sufficient triangle-propagation flag.
