# Cap14, Wagner fibres and a seven-point NO43 core

23 October 2026. Ordinary substantive research following
`LOW15-mu41-research.md`; that earlier note remains unchanged. No solver,
heavy prior replay, Lean job, or final review is used. Assume a hypothetical
68-member SF4 family, H27, global cap14, and the already justified mu41
crowding/cross-star imports. The preceding ordinary P9 cone-average bound
excludes P9 in every point-link, so every exact singleton has size at most
eight. The preceding note gives neighbourhoods 41--43, used degrees 10--14,
and support size 20 or 21.

## Minimum degree12 and support exactly20

For a co-occurring pair u,v, the two opposite singleton classes have size
at most eight, and their opposite pair class has size at most three. Thus

    d(u,v) <= d(u)+d(v)-22.                         (1)

If d(x)=10, every point of its complete triple link has degree at most two.
The intersection graph of its ten triples has maximum degree at most three:
each triple has three points, each used by at most one other triple. A
greedy independent set has size at least ceil(10/4)=3. These are three
disjoint link triples, forbidden. Thus degree10 is impossible.

If d(x)=11, every point of its triple link has degree at most three. An
intersecting SF3 family of point-cap3 has at most six members. Indeed, in
an intersecting seven-member subfamily, every triple has degree sum at
least nine, so each of its points has degree three and every other triple
meets it in exactly one point. The three triples through any point would
then have that point as all three pairwise intersections, a sunflower.
Consequently the exact singleton at x has size at most six at every
actual anchor through x. The other three singletons are at most eight,
so S<=30, while the anchor degree sum D_R<=11+3*14=53. But

    D_R=2N+2-S+T >= 2*41+2-30 =54,

a contradiction. Hence every used point has degree at least twelve.

For degree12, (1) gives point-cap4 in the complete triple link. The
intersecting I8 classification (both P8 and Q8 have a degree-five point)
therefore gives its exact singleton at most seven at every anchor. An
anchor cannot contain two degree12 points: its degree sum would be at
most 52 and its singleton sum at most 30, requiring degree sum at least
54. Nor can an anchor contain a degree12 point and two degree13 points:
its degree sum is at most 52 and singleton sum at most 31, requiring at
least 53. Every anchor through a degree12 point thus has at least two
degree14 points.

Suppose the support had 21 points. Let a,b,c count degrees12,13,14. From
the incidence sum272,

    a+b+c=21,  12a+13b+14c=272,
    2a+b=22,  c=a-1.

Thus a>=1. The 12a members through degree12 points are all distinct,
because no anchor contains two such points. Each contains at least two
degree14 points, demanding at least 24a incidences there. Only
14c=14(a-1) are available, impossible. The support therefore has exactly
20 points, with degree counts

    a+b+c=20,  2a+b=8,  c=12+a,  0<=a<=4.          (2)

These are derived restrictions on a real family, not a support cutoff.

### A tempting stronger local assertion is false

It is false that every SF3 family of point-cap3 has at most ten triples.
There is an eleven-member example, all points of degree three: take on
disjoint supports

    H6 = {012,013,234,235,045,145},
    H5 = {8,9,10; 6,9,10; 6,7,10; 6,7,8; 7,8,9}.

Both components are intersecting SF3. H5 consists of complements of C5
edges on five points. In H6 the doubled pairs 01,23,45 extend cyclically
to the next pair. Each point-link in both components has matching number
at most two, and pair codegrees are at most two. Their disjoint union
is SF3: a triple chosen twice from one component meets its same-component
partner, while cross-component intersections are empty. A literal check
of all165 three-member subsets confirms no sunflower. The degree11
exclusion above genuinely uses the mu41 anchor condition as well.

## The correct 68-member Wagner domain

Since N<=43, the disjointness graph has minimum degree25. Jin with k=3
applies because 25*11>4*68. In the cyclic A3 labelling on eight indices,
edges have differences3,4,5. Deleting empty fibres gives A2 or A1, both
impossible from alpha<=27 and order68, or a surjective A3 map.

Let a_i be fibre masses, b_i the mass of the three adjacent fibres, and
r_i=b_i-25. Independent neighbourhoods and surjectivity give

    r_i in {0,1,2},  sum r_i=4,
    a_i=7+r_i+r_(i+3)+r_(i+5).                    (3)

This is the same inverse incidence identity as in the source, with the
actual parameters68 and25. In particular 7<=a_i<=11.

For each used point x, its star multiplicities t_i satisfy

    sum t_i=d(x) in {12,13,14},
    0<=t_i<=a_i,
    t_i>0 => sum_{j adjacent i}t_j<=r_i.           (4)

These bound missing permissible edges at a particular actual member, and
do not assume a complete blow-up or a matching of missing edges. Any fibre
with r_i=0 consists of actual members of neighbourhood43: all a_i possible
neighbours are used and b_i=25. As shown next, those members use only
degree14 points. Thus every degree12 or degree13 star is confined to the
at most four positive-r fibres. It must occupy at least two fibres because
d(x)>=12 but a_i<=11. These are additional real-incidence restrictions
absent from a bare graph blow-up.

There must be some N=43 anchor. Otherwise the graph has minimum degree26,
and the ordinary Wagner sum contradiction from the preceding note applies:
all eight fibres are occupied but 8*26>3*68. Therefore excluding just the
following N43 local cores suffices for the entire cap14 branch.

## Every N43 anchor has a complete eleven-member core on seven points

Fix R={0,1,2,3} with N=43. The identity
D_R=2N+2-S+T, with D_R<=56 and S<=32, forces

    D_R=56, S=32, T=0.

All four root points have degree14, all four singleton counts equal eight,
and their pair-trace incidences each sum to five. Thus the six pair counts
have equal opposite entries:

    p01=p23=a, p02=p13=b, p03=p12=c,
    a+b+c=5, 0<=a,b,c<=3.

Up to permuting the root, the only triples are

    (a,b,c)=(0,2,3), (1,1,3), (1,2,2).             (5)

There are ten pair-trace members and R itself; no triple-trace members.
This is the *complete* core of members meeting R in at least two points.
For a root pair ij, let E_ij be its family of exterior pairs. These are
distinct pairs, of size p_ij. If p=2 they form a two-edge path; if p=3
they form a triangle, by the ordinary intersecting SF2 classification.

At every root point i, B4 applies to the eight exact singleton tails.
Its near link consists of six triples and is intersecting. Consequently
the union of the three exterior edge families E_ij, j!=i, is an intersecting
edge family. Different incident categories must have intersecting exterior
edges, because otherwise their four-sets intersect exactly in i.
An intersecting simple edge family is a star or a triangle.

**Type (0,2,3).** The two opposite p=3 categories are triangles. Each p=2
category is adjacent to both and every one of its edges covers both
triangles. An edge covering a triangle is an edge of that triangle. The
two distinct edges in a p=2 category use three points, forcing the two
triangle supports to coincide. Every exterior edge is in this one triangle.

**Type (1,1,3).** Again there are two opposite triangles. All four singleton
edge categories connect them, so their edges belong to both triangles.
The two singleton edges incident at any one root point must be distinct:
if they were the same edge e, its occurrence in the triangle category would
give three four-sets with common pairwise intersection {i} union e.
Two distinct edges use three points, so the two triangle supports coincide.

**Type (1,2,2).** At each root point there are two two-edge categories and
one singleton category. Their exterior-edge union cannot be a star with
at least three edges: these three categories then admit three distinct
representatives (the two size-two sets and one singleton satisfy Hall's
condition). Their three exterior edges meet exactly in the star centre,
giving a sunflower with that centre and the root point as core. If the
star has at most two edges, both size-two categories use both edges and
the singleton is in both; choosing that same edge in all three categories
gives a sunflower with three-point core. Therefore the union is a triangle.
The p=2 categories form a four-cycle on the root points. A common two-edge
category fixes all three vertices of its exterior triangle, so equality
propagates around that cycle. Again every edge is on one common triangle.

In all cases, the complete eleven-member core is on R plus a single
three-point exterior set. This support is derived, and the remaining 57
actual members may still have arbitrary exterior support before the global
support theorem is used.

For a fixed root ordering and an exterior triangle, the literal assignment
counts before sunflower filtering are at most9,81,729 for the three types,
respectively. Their sum819 is small. Each p=3 category is fixed, a p=2
category chooses two of three edges, and a p=1 category chooses one.
A complete finite census can retain every literal SF4 core and quotient
only by actual root permutations and exterior-triangle permutations.
This reduction does not yet rule out their arbitrary-support completions.

## Relation to the prior 68-member terminal bridge and R61

The earlier Oct20 note `prior-art68/analysis/prior68-research.md` already
supplies a *new size68* terminal route conditional on maximum degree16,
singleton<=8 and neighbourhood<=44. Its relevant graph domain has minimum
degree24 and images A3 through A6, not the old69 census. Its deletion-cover
bounds (1,2,4,10) apply after a non-R16 sixteen-link is reduced to separated
8+8. The exact finite diagnostics there were not rerun here.

They cannot be applied to a degree12--14 link merely by changing the star
total. Such a link need not have separated8+8, and the four transversal
positions are no longer necessarily exhausted by two two-covers. R61
therefore gives no immediate contradiction for a low-degree fibre or point.
It remains available once a *complete* R16 link has actually been forced;
here that would already contradict cap14. The seven-point N43 reduction
is a more direct next target than assuming a sixteen-link exists.

The core alternatives and formulas above are ordinary arguments. Their
full arbitrary-support completion exclusion is still open in this note.
