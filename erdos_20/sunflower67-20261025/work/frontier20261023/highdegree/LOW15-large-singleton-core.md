# Large singleton pools force a common triangle

23 October 2026. Ordinary research proof, with arbitrary exterior support.
This is a new note; previously hashed sources and notes are unchanged.
No solver, new finite catalogue, or Lean claim is used here.

## Premises and notation

Let F be a finite simple SF4 family of size68. Sunflowers with empty core
are forbidden. For an actual member R={0,1,2,3}, let s_i be its exact
singleton counts, p_ij its exact pair counts, and t_i its exact triple
count on R minus i. Put

    S=sum s_i, P=sum p_ij, T=sum t_i, r_i=sum_(j!=i) p_ij.
    N=1+S+P+T,
    d(i)=1+s_i+r_i+T-t_i,
    D_R=sum d(i)=2N+2-S+T.

Here N counts all members meeting R, including R. Universal exact-trace
bounds are s_i<=10, p_ij<=3, t_i<=1; global triple codegree is at most2.
Each exterior tail family D_i at exact singleton i is intersecting SF3.

The imported B4 lemma says that s_i>=8 makes the near subfamily K_i of
the complete i-link intersecting, where near means meeting R minus i.
We use the I8/I9/I10 classification and isolation: sizes8,9,10 are
respectively P8 or Q8, P9, P10. P-type supports are isolated from K_i;
the five-point Q8 core is isolated from K_i. The usual missing-block
and Q8 exceptional triples cannot be near, because they lie on the
far family's support, which avoids R minus i.

We also use H27, giving mu>=41, and the imported cross-star consequence
HP15 under mu>=41 and Delta<=18. It applies to two actual intersecting
SF3 tail families with distinct centres outside both tail supports, once
the two families are cross-intersecting, and bounds their total size by15.
The source/replayed-certificate boundary is recorded in
`PRIOR_DELTA18_UNLOCK.md` and `prior-delta18-unlock.json`.

For the cap15 consequences only, `LOW15-mu41-research.md` has already
excluded P10 as a subfamily of every point-link. Thus s_i<=9 in that
branch. The crowding26 import bounds the largest three singleton counts
by26, hence S<=34 without using that no-P10 conclusion.

## A local pair-row bound, also in the presence of triple traces

If s_i>=8, then r_i<=6. This statement does not require T=0.

For each j!=i write E_ij for the distinct exterior two-sets in pair-trace
members {i,j} union e. Two edges in one E_ij must intersect: otherwise
their two members and R form a sunflower with core {i,j}. Three such
edges, if present, form a triangle. Indeed, an intersecting three-edge
simple graph is a triangle or a three-edge star, and the latter violates
triple codegree2 on {i,j,star centre}.

If all three incident categories have size at most2, then r_i<=6
immediately. Otherwise some E_ij is a triangle. B4 says that a near
triple {k} union e with k different from j meets each of the three
near triples {j} union f. Its exterior edge e must therefore meet all
three edges f of that triangle. A two-set meeting all three edges of a
triangle is itself an edge of the triangle. Consequently every incident
pair residue is on this same triangle. Each triangle edge can occur
in at most two incident categories, by triple codegree2 on {i} union e.
Again r_i<=6. Additional near triples can only impose more constraints.

## Local triangle structure when the row is at least five

If s_i>=8 and r_i>=5, all incident pair residues lie on one exterior
triangle T_i. This statement also does not require T=0.

The union of the E_ij is an intersecting graph: within a category this
was proved above, and between categories it follows from B4. An
intersecting graph is a star or a triangle. A category of size3 already
forces the triangle case. Otherwise the three category sizes, after
reordering, are (2,2,1) or (2,2,2).

Suppose the union were a star. If it has at least three distinct edges,
the three categories have a system of distinct representatives: every
two categories have union of size at least2 and all three have union
of size at least3. These three distinct star edges, with their three
different root partners, yield a sunflower with core {i,star centre}.
If the union has at most two edges, the size2 categories coincide, and
some edge belongs to all three categories. Those three members form a
sunflower with core {i} union e. Both alternatives are impossible.

Each edge of T_i has multiplicity at most2 across the categories.
Thus 5<=r_i<=6. Every t in T_i has pair-tail degree at least r_i-2>=3.
Its point-link within these pair tails is a simple bipartite graph with
parts R minus i and T_i minus t. Its maximum degree is at most2, by
global triple codegree2. It consequently has a matching of size2:
three distinct pairwise intersecting edges would otherwise be a
three-edge star or a triangle, forbidden by the degree bound and
bipartiteness respectively.

## Common-triangle obstruction

**Theorem.** Under the imported premises above and Delta<=18, an actual
anchor cannot have all s_i>=8, T=0, and all r_i>=5.

First obtain the four local triangles T_i. Form the graph on R with an
edge ij when p_ij>=2. Its minimum degree is at least1, since otherwise
some pair row would be at most3. A shared category of size at least2
uses three exterior points, so T_i=T_j along every edge of this graph.

If the graph is connected, all four triangles coincide. If disconnected,
it consists of a perfect matching. Each root then has two cross categories
of size at most1; its row at least5 forces matching category size3 and
both cross categories size1. Each matching component has one triangle.
The two cross edges incident with any root must be distinct: otherwise
that repeated exterior edge, together with its occurrence in the matching
category of size3, violates triple codegree2 at {i} union e. The two
distinct edges belong to both component triangles and together use
three points. Thus these triangles coincide as well. Denote the common
triangle by T, and put V=R union T.

All far singleton tails lie outside V. For P8/P9/P10 this follows from
support isolation, since the near pair tails use all of T and the
anchor link R minus i uses all other roots. For Q8 its five-point core
is outside V, and its leaves already avoid R. If a leaf were t in T,
the actual Q8 triple {h,k,t}, with both hubs outside V, and the two near
triples through t supplied by the matching above would form a sunflower
in L_i with core {t}. Thus Q8 leaves also avoid T.

Choose a positive pair category kl, an actual member B={k,l} union e,
and the complementary roots i,j. Both D_i,D_j avoid V. If tails U in D_i
and W in D_j were disjoint, their lifts {i} union U, {j} union W, and B
would be three pairwise disjoint members. Hence D_i,D_j are cross-
intersecting. Their centres are outside both supports, and each has
at least8 members. HP15 gives 16<=|D_i|+|D_j|<=15, a contradiction.

Although T=0 is convenient for the intended profile applications, the
proof of the theorem itself uses only the displayed pair members,
the anchor, B4, and isolation. It therefore remains valid with T>0
provided all s_i>=8 and all r_i>=5.

## Consequences N<=45 at cap15 and N<=47 at cap16

At cap15, D_R<=60 and S<=34 imply N<=46. Equality N=46 forces
D_R=60,S=34,T=0. The already proved no-P10 result gives the unique
sorted singleton pattern (8,8,9,9), all four root degrees15, and rows
(6,6,5,5). The common-triangle theorem excludes it. Thus every actual
anchor has N<=45 under cap15.

At cap16 the same identity gives N<=48. Equality forces
D_R=64,S=34,T=0, with every root degree16. The largest-three bound26
forces the smallest singleton to be at least8. Since every singleton
is at most10, the only sorted patterns are

    (8,8,8,10) and (8,8,9,9).

Their pair rows are respectively (7,7,7,5) and (7,7,6,6). Every root
has singleton count at least8, so the local row bound r_i<=6 already
contradicts either pattern. Thus every actual anchor has N<=47 under
cap16. This argument does not exclude P10 or P9 at cap16.

## A literal triple member bounds its omitted pair row by four

Suppose Q_l=(R minus l) union {z} is an actual exact triple member,
and s_j>=8 for each j!=l. For a pair member {l,j} union e, B4 in L_j
makes its near triple {l} union e intersect Q_l minus j. The only
possible intersection is z, so z lies in every incident edge E_lj.

Removing l,z from these pair members produces a simple bipartite graph
between R minus l and exterior points other than z. Each vertex degree
is at most2 by triple codegree2. It has no matching of size3, because
such a matching gives a sunflower with core {l,z}. Every path or even
cycle of maximum degree2 has at most twice as many edges as its maximum
matching; summing over components gives r_l<=4.

This guard uses B4 at all three other roots. It is not asserted when
one of their singleton counts is below8.

## The complete P9/P10 point-link complement lemma

If an intersecting SF4 family I has a **complete** point-link H=P9 or
P10 at a, then |I|<=20. Here complete means every member of I containing
a is one of the displayed cones. The ordinary proof is also present
in the frozen prior paper, `paper/main.tex`, lines1124--1144.

Put W=supp(H), so |W|=6. Each member of I avoiding a meets every H
triple, hence uses at least3 points of W. Let b count four-sets inside
W, and e count members with a three-point trace on W.

For P10, the triple transversals are its ten blocks. Each internal
four-set contains two blocks, and each block has only one remaining
triple-capacity unit after its a-cone. Therefore e+2b<=10 and
|I|=10+b+e<=20.

For P9=P10 minus B, every internal four-set contains at least one of
the nine surviving blocks. If e_H counts extensions of these blocks,
then e_H+b<=9 by the same capacity subtraction. The only other triple
transversals are B and W minus B. If both extension classes occur,
intersection forces every pair of their exterior points to coincide;
simplicity then leaves at most one member in each class. If just one
class occurs, triple codegree2 bounds it by2. Their combined count is
therefore at most2, and |I|<=9+9+2=20. Internal four-sets were included
in the count throughout.

## N45 with all singleton counts at least eight: triple traces

Assume cap15, N=45 and all s_i>=8. Since s_i<=9 and S<=34, the sorted
patterns are (8,8,8,8), (8,8,8,9), (8,8,9,9). The degree identity gives
S>=32+T. If T>0 only the following arithmetic cases remain.

* S=33,T=1. All root degrees are15. At the omitted root l the pair row
  is 14-s_l, hence at least5, contrary to the preceding bound4.
* S=34,T=1. The total root-degree deficit from15 is1. An omitted root
  with s_l=8 has r_l>=5 and is impossible. An omitted root with s_l=9
  can have r_l<=4 only when d(l)=14 and r_l=4.
* S=34,T=2. All root degrees are15. An omitted root with s_l=8 has row5
  and is impossible. Thus both omitted roots have singleton count9
  and pair row4.

In each remaining case choose an actual Q_l as above. Its far singleton
family D_l is P9. Since r_l=4 and each pair edge contains z, the near
family uses z. P9 isolation therefore makes all nine far triples avoid z.
They already avoid R minus l. Hence Q_l avoids all nine far cones at l.

Now take I to be all actual members disjoint from Q_l. It is intersecting,
because two disjoint members of I together with Q_l would be an
empty-core sunflower. Its complete l-link is exactly D_l=P9: every
other member through l meets R minus l and therefore meets Q_l.
The complete-link lemma gives |I|<=20. Even the weaker prior N<=46
would give |F|=N(Q_l)+|I|<=46+20=66, a contradiction. Thus T=0 in
every hypothetical all-large-singleton N45 profile.

## N45 with all singleton counts at least eight: no triple traces

Continue with T=0. Call a root high when r_i>=5. Each high root has
the triangle T_i and matching property proved above, so its whole far
family avoids R union T_i.

If S=32, all singleton counts are8, all root degrees are15, and all
rows are6. The common-triangle theorem applies directly.

If S=33, the maximal rows allowed by cap15 are (6,6,6,5), with one
unit of total deficit. If all rows are at least5, use the theorem.
Otherwise the unique low root has singleton count9 and row4, and
the other three roots have row6. The sum of their three internal
pair counts is (18-4)/2=7.

If S=34, the maximal rows are (6,6,5,5), with two units of total
deficit. If all rows are at least5, use the theorem. If exactly one
root is low, its row q is3 or4, and the sum of pair counts among the
three high roots is (20-2q)/2=10-q>=6.

In either three-high-root case, the graph of pair counts at least2
on those three roots is connected. Otherwise it has at most one such
edge, and its total pair count would be at most3+1+1=5. Their triangles
therefore coincide, say T. The low root has a positive pair category
to a high root; an actual member in that category has exterior edge
in T. Its complementary roots are both high. Their far tails avoid
R union T, so this member supplies the cross-intersection witness
and HP15 contradiction. No isolation assertion about the low root
is needed.

The only case with exactly two high roots has S=34. Its high roots
have singleton8 and row6 each; its low roots have singleton9 and
row4 each. Write p_HH and p_LL for the internal pair counts of these
two root pairs. Subtracting the two row sums gives

    p_HH-p_LL=(12-8)/2=2.

Thus p_HH>=2 and p_LL<=1. The two high triangles coincide, say T.
Each low root has row4 and at most one member in the low-low category,
so one of its two categories to high roots has size at least2. Those
two distinct edges use all three points of T. Its near family thus
uses all of T, and its P9 far support avoids T by isolation. All four
far families now avoid R union T. A positive high-low pair supplies
a witness for the complementary high/low pools, of total size17,
again contradicting HP15. This does not presume that the low-low
category itself is supported on T.

Consequently every N45 profile under cap15 with all s_i>=8 is excluded.
Any remaining N45 profile has a singleton count at most7. Its sorted
singleton pattern must be one of

    (6,8,9,9), (7,7,9,9), (7,8,8,9), (7,8,9,9).

The first three have S=32 and T=0; the last has S=33 and T<=1.
No exclusion of these remaining patterns is claimed here.

## An invalid shortcut that is not used

Merely finding an actual Q outside a P9/P10 star's seven-point support
does not make the star the complete point-link in the intersecting
disjoint complement of Q. That complement can retain additional cones
whose tails are outside the six-point P support. Intersection of four-
sets through the centre puts no intersection requirement on their tails.
Thus the generic inference |D(Q)|<=20, and the proposed generic no-P9
or no-P10 deductions from it, are unjustified and are not conclusions
of this note. The special Q_l above contains every other root point,
which explicitly removes every near cone and repairs the completeness
condition in exactly that application.
