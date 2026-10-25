# Independent ordinary bridge for the cap15 A3 and 8+7 cover argument

24 October 2026. Source inspection and ordinary proof reconstruction,
with read-only extraction from the existing receipt. No producer or
finite search was executed here. This checks the family and graph
bridges; the numerical cover maxima remain the explicitly identified
finite computation below. No R15 classification is needed in this note.

## Inspected inputs and outcome

The inspected sources are `LOW15-A3-star-fibre-reduction.md`,
`LOW15_classified_cover_probe.py`, `LOW15-classified-cover-probe.json`,
`LOW15-eight-seven-cover-closure.md`, and the literal I7 catalogue in
`D17-I7-classification-route.md` and the frozen prior paper.

No mathematical or implementation flaw was found in the A3 transfer,
the arbitrary-support cover bounds, the 8+7 domain, or the two incidence
reductions. The receipt contains29 relevant 8+7 models and121 prescribed
deletions per model, hence3509 relevant cases. Its R15 records are a
separate domain and are not used. The reported uniform maxima for
deletion sizes0,1,2 are respectively2,4,10.

The following reconstruction makes the support and gluing boundaries
explicit. In particular, the thirteen Q8 gluings can be justified
directly, without trusting the producer's170 rejection tests.

## A3 arithmetic and the star support

Assume |F|=68, Delta<=15, H27 and the ordinary NO44 conclusion. The
disjointness graph is triangle-free, has independence number at most27,
and minimum degree at least25. Jin's strict k=4 threshold holds:
25*14>5*68. The established empty-fibre reduction gives a surjective
Andrasfai image A_k with k<=4. A1,A2 contradict their independence
sums; A4 has eleven neighbouring-fibre masses at least25, whose sum
would be at least275 although it equals4*68=272. Thus the image is A3.

Use indices modulo8 and adjacency differences3,4,5. If a_i is a fibre
mass and b_i=a_(i+3)+a_(i+4)+a_(i+5), then25<=b_i<=27. Put r_i=b_i-25.
Expanding three neighbouring masses and summing gives exactly

    r_i in {0,1,2}, sum r_i=4,
    a_i=7+r_i+r_(i+3)+r_(i+5).

For a degree15 point-star, let t_i be its mass in fibre i and S its
occupied index set. A star member has no star neighbour in the
disjointness graph, so q_i=sum_(j adjacent i)t_j<=r_i on S. Therefore

    sum_(i in S) t_i deg_(A3[S])(i)=sum_(i in S) q_i<=4.

This bounds a nonempty induced edge pattern by a single edge, two
disjoint edges of endpoint weights1, or a two-edge path with all
weights1. Every other pattern contributes at least6. Any additional
occupied indices must be isolated in this induced graph.

A chord {0,4} has possible isolated indices2,6, which are adjacent.
Using both gives only four star members and no additional isolated
index. Using at most one gives total at most11: if endpoint mass is e,
its two r values consume at least e, while the isolated index's mass
is at most7+(4-e). For a two-edge path, its centre r is at least2 and
each endpoint r at least1, exhausting the total4. Its possible isolated
indices have mass7, and at most one exists; the total is at most10.

The remaining edge, up to a dihedral symmetry, is {0,3}. Its possible
isolated indices are1,2. Both must be present to obtain total15. Thus

    S={0,1,2,3}, t_0,t_3 in {1,2}, t_1,t_2>=4.

The two endpoint bounds are q_0=t_3<=r_0<=2 and its reciprocal. The
interior bound follows because, for e=t_0+t_3, each interior fibre
has mass at most11-e while the two interior weights sum15-e.

If S is independent, it lies in a three-index cyclic window. Such a
window is a neighbouring-fibre union and has mass at least25. Its
at least10 nonstar members meet every cone of the complete link.

In the nonindependent case, deleting the t_3 actual cones in fibre3
leaves every nonstar member in fibres0,1,2 as a four-cover. The count is

    a_0+a_1+a_2-(15-t_3)=10+t_3+r_5.

It is at least11 for a one-cone deletion and at least12 for a two-cone
deletion. These deductions use only the absence of graph edges between
nonadjacent image indices, not completeness of any allowed bipartite
graph. The symmetric deletion at fibre0 works identically.

## Every rho8 degree15 link is in the 8+7 domain

Choose an actual link triple A with exactly eight disjoint triples H.
They are intersecting, since two disjoint members of H together with
A would be an empty-core sunflower. The seven-member complement K
is intersecting by B4. The universal I8 classification gives P8 or
Q8 for H; the arbitrary-support I7 theorem gives one of H0,...,H7 for K.

For P8, an additional triple meeting its six-point support can only
be a deleted P10 block. Such a block is disjoint from A, because
the whole support of H avoids A. It therefore cannot belong to K.
Thus the two supports are disjoint. The two P8 omission types, with
omitted blocks intersecting in one or two points, give2*8=16 models.
The complete two-orbit P10 omission check is also present in the
independent D16 cover receipt, with orbit sizes30 and15; only that
universal component identity is used here, not its degree16 bound.

For Q8, its five-point core avoids K. The only isolation exceptions
are a hub plus both leaves; these too are supported in H's support,
avoid A, and cannot lie in K. Its two distinct leaves may still lie
in K's support. All remaining points of K are outside the core.
This is precisely the gluing boundary, with no ambient support cutoff.

## Exact ordinary criterion for a Q8 leaf gluing

Fix Q8 with its core disjoint from K. A shared leaf v is permitted
if and only if the residual point-link of v in K is intersecting,
meaning no two K triples intersect exactly in {v}.

To prove this, all pairs of Q8 triples have an intersection containing
a core point, so two Q8 triples and one K triple cannot be a sunflower.
A core-only Q8 triple avoids K altogether; with two intersecting K
triples it cannot be a sunflower either. A Q8 leaf triple meets a K
triple only at its leaf v, if at all. It therefore forms a sunflower
with two K triples exactly when their mutual intersection is {v}.
These exhaust all triples from the union. The two leaves impose their
conditions separately; there is no additional joint gluing condition.

For the eight literal I7 templates, the permitted vertices are

| I7 type | Vertices permitted as shared Q8 leaves |
|---|---|
| H0,H1,H3,H4,H5 | none |
| H2,H6 | 0 |
| H7 | 5,6 |

Here is a direct small witness check. Any I7 vertex of degree at least4
is forbidden, because an intersecting SF2 graph has at most3 edges.
For the remaining forbidden vertices, the following residual edge pairs
are disjoint. Each pair is obtained by deleting the indicated vertex
from two literal I7 triples.

| Type | Forbidden low-degree vertex: residual edge pair |
|---|---|
| H0 | 0:12,34; 1:02,34; 2:01,35 |
| H1 | 0:12,34; 1:02,35 |
| H2 | none |
| H3 | 0:13,24; 1:03,25; 2:04,15 |
| H4 | 0:23,45; 1:34,25 |
| H5 | 0:14,25; 1:04,25; 2:34,05; 3:24,05 |
| H6 | 1:34,25; 2:34,15 |
| H7 | 2:03,14; 3:02,14 |

The allowed vertex0 of H2 has one residual edge12. Vertex0 of H6
has the two intersecting edges35,45. Vertices5,6 of H7 each have
the single residual edge01. This proves both sides of the table.

The leaves are unordered and distinct. Thus each type has its
both-fresh gluing; H2,H6 have one additional one-shared gluing each;
H7 has two one-shared gluings and one both-shared gluing. The total is
8+1+1+2+1=13, exactly the thirteen Q8 records in the receipt. Equivalently,
the enlarged producer domain has seven sets of1+6+15 gluings and one
set of1+7+21, for183; the criterion accounts for all170 rejected ones.

## Arbitrary-support covers and exact capacity reductions

Let L be any of these29 complete links, W its full support, and D any
set of at most two prescribed link triples. An actual four-member Q
avoiding x and meeting every remaining x-cone must meet every triple
of L minus D. At least13 triples remain. Every point lies in at most6
link triples, so two points cover at most12. Hence |Q intersect W|>=3.

Let C3 be all three-subsets of W covering L minus D, and P4 all
four-subsets covering it but containing no C3. If Q has exactly three
points in W, those points form a C3. If Q has four points in W, it
either contains a C3 or is itself a P4. Thus, on arbitrary ambient
support, simplicity and global triple codegree2 give

    number of actual x-avoider covers <=2*|C3|+|P4|.

This is a union bound, so a member containing several C3 sets causes
no undercount. There is no assumption on how exterior points coincide.

The source's two optional refinements are valid:

* If all C3 and P4 generators contain a pair P, every actual cover
  contains P. Its global codegree is at most6, and each prescribed
  x-cone containing P already consumes one unit. The bound is6 minus
  the number of all such cones in L.
* If C3 is empty, every actual cover is an internal P4. If all P4
  contain z, let V be the union of their points other than z. Each
  actual cover consumes three ambient triple capacities {z,a,b}, with
  {a,b} a pair in V. Each capacity is at most2, reduced by one if
  {z,a,b} itself is a link triple, since its prescribed x-cone exists.
  Summing these capacities and dividing by3 gives the stated bound.

In both refinements, cones deleted from the covering requirement still
exist in F and must still be charged against capacity. The source does
this correctly by counting against the full L. Its finite bounds may
overcount incompatible candidates, which only weakens the conclusion.

## What the finite source actually checks

The source represents sets by bit masks and tests a three-member
sunflower by equality of the three pairwise intersections, including
the empty intersection. It checks link cardinality, distinctness and
point degree. For each supporting three- or four-set C it computes
exactly the link members missed by C. It sends C to precisely those
deletion sets containing that missed set, with total deletion size at
most2. This is a complete relation, not a sampling of deletions.

For each deletion it removes four-covers containing a C3 from P4,
computes the union bound and the valid refinements above, and records
the maximum separately for d=0,1,2. There are121 deletions per link.
The complete receipt has45 links because it additionally includes16
R15 models. Its5445 cases therefore contain3509 relevant 8+7 cases.
The R15 exceptions neither enter nor invalidate the 8+7 maxima.

The relevant extracted maxima are

| I8 part | Models | Full covers | One deletion | Two deletions |
|---|---:|---:|---:|---:|
| P8, omitted blocks intersect1 | 8 | 0 | 4 | 10 |
| P8, omitted blocks intersect2 | 8 | 2 | 4 | 10 |
| Q8, all allowed gluings | 13 | 2 | 4 | 8 |

Only the P8 intersection1 two-deletion bound uses a refinement of the
raw union bound12. Every other entry already follows from raw counts.
The present cap15 domain also excludes that P8 type by an earlier
ordinary argument, so retaining it is a harmless enlargement.

Combining these bounds with the A3 requirements excludes rho8 at a
degree15 point:10 full covers exceed2, at least11 one-deletion covers
exceed4, and at least12 two-deletion covers exceed10.

## Assurance boundary and byte identities

This note independently reconstructs the graph and family bridges and
the entire Q8 gluing criterion. It inspects, rather than independently
executes, the finite covering relation. Thus the precise finite
predicate still used is that the displayed29 literal links, under all
121 deletions, have the recorded capacity bounds. The producer and
receipt are byte-bound as follows:

| Input | SHA256 |
|---|---|
| LOW15-A3-star-fibre-reduction.md | 0b088edeecd0a486f19050422b446d871e31b87fc4098994f5aa1241f665455c |
| LOW15_classified_cover_probe.py | 8a0dd2733dafb365a51c26b3512394bb6b7c88399ef5674589e8872ba9c199c3 |
| LOW15-classified-cover-probe.json | 2c13e66d1aa9f8dc1c4319b60c89684b000e571acfa08edc2d33966b14fd271d |
| Frozen prior paper/main.tex | 4aa36c9d56af5a8e3bdb44749107820549a73e0d3405e6c700104fa4c30e5c21 |
| D17-I7-classification-route.md | a86e80d8377f24218194461c7e2dd92ffe44c3d6b4a505240bd050f129dcb504 |

The source hash in the receipt matches the inspected source. Its full
covering-relation digest is
`db3a1cf1d4f61296d9bee807dba8a4605c47892023ebb1d595c677168d5bc8af`.
No source, original note, or receipt was modified by this inspection.
