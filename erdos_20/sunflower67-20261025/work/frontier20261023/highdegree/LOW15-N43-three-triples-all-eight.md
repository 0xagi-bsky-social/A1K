# N43, three triple traces and four singleton8 pools

24 October 2026. Ordinary proof development under the cap15, mu41,
size68 domain with B4, I8/isolation, global pair/triple capacities and
HP15. No solver or Lean result is used. This excludes the stated
subcase, while retaining the singleton7 case as a separate task.

Let R=0123, N(R)=43, s=(8,8,8,8), and t=(0,1,1,1). Write the three
triple members Q_i=(R minus i)+z_i for i=1,2,3. All centres are outside R.
The pair total is7. The row bounds are r0<=3 and r1,r2,r3<=4, with total14.
Every pair category is at most2: it is constrained to contain a triple
centre by intersection of an appropriate near link, so triple-codegree2
applies. Solving these row equations, up to permutation of1,2,3, gives
exactly the following four profiles in order01,02,03,12,13,23:

    A: (0,1,1,2,2,1), rows (2,4,4,4);
    B: (0,1,2,2,1,1), rows (3,3,4,4);
    C: (0,1,2,2,2,0), rows (3,4,3,4);
    D: (1,1,1,1,1,2), rows (3,3,4,4).

For completeness, if r0=2 the other rows are4. Its entries cannot be
(0,0,2), which would require an opposite category3; thus they are(0,1,1),
giving A. If r0=3, one other row is3 and two are4. Its entries are(0,1,2)
or(1,1,1). The three possible positions of the deficit in the first case
give B,C or a category3; the second case gives D.

Let D_i be the size8 far tail family at i, and K_i its intersecting near
link. We use the matching lemma proved explicitly in
`LOW15-N43-four-triples-exclusion.md`: two disjoint edges in the w-point
link inside K_i imply every D_i triple avoids w. Core isolation excludes
core occurrences, and a far Q8 leaf at w would supply a third disjoint
edge between the far hubs. This retains arbitrary overlap of other leaves.

If i,j are both in{1,2,3}, each exterior edge in category ij contains
z_i,z_j. A category of size2 therefore implies z_i=z_j. If all three
centres equal a, such a category already has two extensions containing
{i,j,a}, and Q_k for the third omitted index supplies a third, impossible.
This immediately excludes A,C, whose size2 categories connect1,2,3.

## Profile B

Here z1=z2=a. Put z3=b; they differ by the preceding capacity argument.
The categories13 and23 have their sole edge ab. Category03 consists
of two edges bu,bv, with u!=v. Neither contains a, since Q1 and Q2
already saturate triple {0,3,a}. Category02 has an edge ac.

Inside K0, the triples 2ac and 3bu,3bv must intersect. The point a is
absent from the latter edges, so c is their common point b. Thus the
actual E=02ab occurs.

In K1 the a-link has disjoint edges03 and2w, where aw is either edge
of category12; its b-link has disjoint edges02 and3a. In K3 the a-link
has disjoint edges02 and1b, while its b-link has disjoint edges0u and1a;
the latter are disjoint because u is exterior and u!=a. Thus both
D1,D3 avoid a,b. The actual E avoids both centres and both tail supports,
so two disjoint tails, one from each pool, would make an empty sunflower
with E. The pools cross-intersect and violate HP15 since8+8>15.

## Profile D

Here z2=z3=a and z1=b, with a!=b. Categories12,13 each have edge ab;
category23 has two edges au,av. Category01 has an edge bd with d!=a,
because Q2,Q3 saturate {0,1,a}. The other categories02,03 have edges
ae,af. Intersection inside K0 with its triple1bd forces

    e,f in {b,d}.

All of D1,D2,D3 avoid a,b. At root1, the a-link has disjoint edges03
and2b, and the b-link has disjoint edges0d and2a. At root2, the a-link
has disjoint edges01 and3u, and the b-link has disjoint edges03 and1a.
At root3, the a-link has disjoint edges01 and2u, and the b-link has
disjoint edges02 and1a. The named exterior letters cannot be root labels,
and d!=a, so these displayed pairs really are disjoint.

If e=b, the actual02ab witnesses cross-intersection of D1,D3. If f=b,
the actual03ab does so for D1,D2. Either contradicts HP15. Hence e=f=d.

Now examine the a-link inside K3. Its five edges are

    01, 0d, 1b, 2u, 2v.

The edges0d and1b are disjoint. To avoid a three-matching, each of2u,2v
must meet their four endpoints. Since u,v are exterior, distinct, and
different from a, this forces {u,v}={b,d}. In particular23ab is actual.
At root0, the a-link has disjoint edges13 and2d, and the b-link has
disjoint edges23 and1d. Thus D0 also avoids a,b. The actual23ab now
witnesses cross-intersection of D0,D1, again contradicting HP15.

All four scalar profiles are excluded, proving that no N43 anchor has
all four singleton counts8 and exactly three triple members.

## One further mixed-singleton elimination

The necessary local-signature census leaves two T3 profiles with
s=(7,8,8,8), t=(0,1,1,1), all root degrees15. One is

    p=(0,2,2,2,2,0).

Its categories12 and13 still force z1=z2=z3, and the same third-extension
argument excludes it. This does not require B4 at the singleton7 root0.
The other profile p=(1,1,2,2,1,1) is not excluded by this note.
