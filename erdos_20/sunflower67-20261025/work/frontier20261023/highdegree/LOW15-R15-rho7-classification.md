# Ordinary classification of a size15 SF3 family with rho exactly7

23 October 2026. New ordinary proof development, conditional on the
explicit prior seven-member intersecting-family catalogue and its
arbitrary-support trace obstruction. This is not a final audit, a new
catalogue replay, or a Lean theorem. No solver or support enumeration
is used in the proof below.

**Theorem.** Let L be a finite simple triple family with no three
distinct members having equal pairwise intersections, including empty
core. Assume |L|=15 and

    rho(L)=max_(A in L) #{T in L:T intersect A is empty}=7.

Then L is isomorphic to the canonical R16 family with one triple
removed. In particular it extends to R16, has exactly ten used points,
and has no point of degree below3. The theorem does not cover rho<=6.

The R16 model has four distinct hubs u,v,a,b and disjoint triads D,E,
all ten points distinct:

    {u+P,v+P : P in binom(D,2)}
      union binom({u,v,a,b},3)
      union {a+P,b+P : P in binom(E,2)}.                    (R)

## Imported finite classification and universal elementary facts

The frozen source is
`work/frontier20261020/prior-art68/repository/paper/main.tex:465--529`,
within the universal R16 proof. It gives an arbitrary-support proof
that an intersecting SF3 family of size7 has support at most7, then
the complete eight-type catalogue H0,...,H7 and every permissible
mixed trace. It does not impose an assumed ambient support cutoff.
The relevant catalogue entries are reproduced below where used.
Its finite catalogue verification remains an explicit imported
dependency; this note does not rerun it or strengthen its assurance.

For every SF3 family, point degree is at most6 and pair codegree at
most2. A point-link is an SF2 graph, whose maximum degree and matching
number are at most2. An intersecting SF2 graph has at most3 edges,
with equality a triangle. A two-set covering all edges of a triangle
is one of its three edges. These are universal elementary facts.

Choose A in L with exactly7 disjoint triples, put H=D_L(A),
W=supp(H), and K'=L minus H. H is intersecting: two disjoint members
of H with A would be three disjoint triples. It has one of the eight
imported types. No K' triple is wholly in W, since W avoids A and
such a triple would also belong to H. Write K0 for the K' triples
avoiding W. K0 is intersecting, and |K0|<=7 since every H triple is
disjoint from all of K0. There are exactly8 triples in K'.

## Eliminate H0,H1,H3,H4,H5

H3,H4 permit no mixed triples, so |K0|=8, contradiction. For H0,H1,H5
the only mixed traces are at most three specified pairs of W, each
already of codegree1 in H. Thus there are q mixed triples with
1<=q<=3 and k=|K0|=8-q>=5. Each allowed pair P is avoided by an
actual H triple. If P+r is a mixed triple, every K0 triple must contain
r; otherwise that K0 triple, P+r and the H triple avoiding P would
be three pairwise disjoint triples.

If two distinct exterior centres r occur, at least five K0 triples
contain their common pair, violating pair-codegree2. If all mixed
centres are the same r, its degree is at least k+q=8, violating degree6.
These cases are impossible already at size15.

## Eliminate H6

Use the literal catalogue

    H6={134,234,125,035,135,045,245},

whose only mixed traces are {0} and {1,2}. The H block125 avoids
every K' triple except a possible mixed12+a. Since |K'|=8 and rho<=7,
this mixed triple must occur; it is unique because12 already has
codegree1. Every K0 triple contains a, using the H block035 which
avoids12+a as the empty-sunflower witness.

Write q for the number of mixed triples0+e, and k=|K0|. Then k+q=7.
In the point-link of0, the two existing edges35,45 lie wholly inside
W, while all e are exterior. Thus the e form an intersecting SF2
graph, since a matching of two exterior edges and either existing
edge would be a three-matching. Hence q<=3. The point a already
occurs in12+a and in k K0 triples, so k<=5 and q>=2.

If q=3, the exterior edges form a triangle T. If a avoids T, each
K0 triple, after removing a, must cover T and is one of its three
edges, so k<=3, contrary to k=4. If a lies in T, it occurs in two
mixed0+e triples as well, giving degree at least1+4+2=7. Thus q!=3.

If q=2, the two exterior edges are {z,r},{z,s} with r!=s, and k=5.
The six incidences12+a and K0 already saturate degree6 at a, so a
avoids both exterior edges. Each of the five K0 residual edges after
removing a must meet both {z,r},{z,s}. Such an edge either contains
z or is {r,s}. At most two contain z by pair-codegree at {a,z}, and
at most one equals {r,s}. Five are impossible. This eliminates H6.

## Eliminate H7

The literal catalogue is

    H7={023,024,034,124,134,015,016},

with mixed traces {5},{6},{2,3},{5,6}. The block023 avoids all K'
triples except a possible23+a, so that unique mixed triple is
mandatory. The H block015 shows that every K0 triple contains a.
The block016 shows that every mixed5+e has a in e; similarly015
shows the same for every mixed6+e.

Let p,q count the mixed5+e,6+e triples, t count mixed56+r triples,
and k=|K0|. Pair-codegrees give p,q,t<=2. Counting K' and the degree
of a gives

    k+p+q+t=7,           1+k+p+q<=6.

Hence t=2 and k+p+q=5. The two56+r triples have distinct exterior
centres r,s; neither equals a, since the displayed six occurrences
already saturate degree(a). The seven K' triples other than23+a
are exactly D_L(023), so they form an intersecting family. Every
K0 triple must meet56+r and56+s and contains a, hence must be
{a,r,s}. Thus k<=1. The bounds p,q<=2 now force k=1,p=q=2.

But the point-link of5 has its existing edge01, the two mixed edges
{a,u},{a,v}, and the two edges{6,r},{6,s}. All four latter edges
avoid0,1. To avoid a three-matching with01 they would have to be
pairwise intersecting, whereas an intersecting SF2 graph has at
most3 edges. They are four distinct edges, contradiction.

Only H2 remains.

## The six-core form for H2

The H2 reduction in the frozen R16 proof, lines574--611, is an
ordinary pair-capacity and forbidden-pair argument independent of
the final cardinality16. Rename its six-triple core as

    {u+P,v+P : P in binom(D,2)},       |D|=3,

and its seventh member as uvb. Pair capacities and the displayed
opposite-hub witnesses forbid any further triple meeting D. All
remaining triples are of the forms uvw, u+e, v+f, or avoid
{u,v} union D entirely. Call the latter family K*. It is intersecting
and has size k<=7. There are q=1 or2 triples uvw.

If q=1, the only further u/v triples are at most one ubr and at
most one vbs. If q=2, write the two triples uva,uvb; the only further
u/v triples are uab and vab, each optional. All exterior letters
here avoid u,v,D; those required distinct below are explicitly stated.
These shape restrictions are the same ordinary restrictions used
before the final count in the prior size16 proof.

## One uv-triple

Suppose uvb is the only uv-triple. The size equation is

    6+1+(number of u/v extras)+k=15.

There must be at least one extra since k<=7.

If there is just one, say ubr, then k=7. Every K* triple meets
{b,r}, using ubr and an opposite v-core triple as the empty-sunflower
witness. The exclusive b-star and exclusive r-star in K* each have
at most3 triples: their residual edges are disjoint from a known
edge of their point-link and must be intersecting SF2 graphs.
The pair{b,r} already occurs in ubr, so at most one K* triple contains
both b,r. If such a joint triple brt occurs and the exclusive b-star
had size3, its residual triangle would have an edge avoiding t.
In the point-link of b this edge, the existing edge uv, and the new
edge rt would be three disjoint edges. Thus in the joint case the
exclusive b-star has size at most2. In either case k<=6, contradiction.

There are therefore both extras ubr and vbs and k=6. Each K* triple
meets both {b,r} and {b,s}. If r!=s, the triples avoiding b contain
{r,s} and number at most2. Those containing b have a residual edge
meeting r or s; each of these two points has only one remaining
pair-capacity unit with b, after ubr and vbs. Thus at most2 more
occur, giving k<=4, contradiction.

Hence r=s=a. The pair{a,b} is saturated by uab,vab, so K* splits into
exclusive a- and b-stars. Each residual graph is intersecting SF2:
the known b-link contains the triangle on u,v,a, and the known a-link
contains the path u-b-v, both disjoint from the respective new
residual edges. Each has at most3 edges. Since k=6, both are triangles;
intersection of K* makes their edges cross-intersecting, so the two
triangles are the same triad E. All E points avoid u,v,a,b,D.
The resulting L is exactly (R) minus the hub triple uva.

## Two uv-triples

Suppose uva,uvb occur, with a!=b. Put e for the number of optional
extras uab,vab. Then k=7-e.

If e=0, the six-core and the two uv-triples form Q8 with hubs u,v,
triad D and leaves a,b. Every K* triple must meet {a,b}; otherwise
it is disjoint from all8 Q8 triples, contradicting rho<=7. Each of
a,b has degree at most3 within K*: two disjoint residual edges at
that leaf, together with the Q8 leaf edge uv, would form a
three-matching in its point-link. Hence

    k<=d_K*(a)+d_K*(b)<=6,

contrary to k=7.

If e=1, say only uab occurs, then k=6. Every K* triple meets {a,b}
by the opposite v-core empty-sunflower witness. The exclusive a-
and b-stars each have at most3 edges, and at most one joint abt
triple can occur. In the joint case, a size3 exclusive a-star would
give a residual triangle; an edge of that triangle avoiding t,
the known edge uv, and the joint edge bt are a three-matching in
the a-link. Thus it has size at most2; the same holds for the
exclusive b-star. A joint triple would therefore give k<=5.

So there is no joint triple. Both exclusive stars have size3,
and their residual triangles coincide by cross-intersection of K*.
The result is (R) minus the missing hub triple vab.

If e=2, then k=5. Again every K* triple meets {a,b}, and the pair
ab is saturated, so the stars are exclusive. Each residual graph
is intersecting SF2 with at most3 edges. They have sizes3 and2;
the size3 graph is a triangle E, and the two opposite edges must
be two of its edges to meet all three. Adding the third edge at
the smaller star produces exactly (R). Thus L is R16 minus one
outer hub-plus-triad-edge triple.

These cases exhaust H2 and prove the theorem.

## Useful degree consequences for an actual seven-disjoint anchor

Deleting a hub triple from R16 leaves degree multiset

    4,4,4,4,4,4,5,5,5,6.

Deleting an outer triple leaves

    3,3,4,4,4,4,5,6,6,6.

In the second case, the only degree3 points are the two triad vertices
of the deleted outer edge. The only remaining actual triple containing
both of them uses the other hub of that triad, of degree6. Consequently
no actual triple in an R16-minus-one family has point-degree pattern
(2,4,4) or (3,3,4).

The theorem applies to a degree15 point-link whenever it has at most7
disjoint triples per actual member and some actual anchor realizes7.
The N44 low-root applications have exactly this equality guard. No
claim that every size15 rho<=6 family extends to R16 is made here.
