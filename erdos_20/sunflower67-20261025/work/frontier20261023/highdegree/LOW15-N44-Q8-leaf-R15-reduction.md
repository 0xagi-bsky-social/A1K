# The remaining N44 anchors force an R15 link

23 October 2026. Ordinary development, with arbitrary exterior support.
This note uses the previous four-profile reduction and explicitly separates
the newly supplied R15 classification from the literal reduction to it.
No enumeration, LP, or Lean process was run.

## Domain and four profiles

Let F be a finite simple SF4 family of size68, with empty-core sunflowers
forbidden and global degree cap15. Assume H27, B4, I8 classification and
isolation, and the stated cross-star import. The existing ordinary cap15
arguments give no P9 or P10 in any point-link, all exact singletons<=8,
and N(Q)<=44 at every actual Q. The cap16 proof
`D16-P8-no-two-cover-exclusion.md` applies in this smaller degree domain:
its hypotheses use only cap<=16, N<=45 and the named no-P9/imported facts.
Thus an intersecting size8 subfamily is two-cover P8 or Q8.

Suppose N(R)=44 for R={0,1,2,3}. The preceding ordinary note
`LOW15-N44-N43-core-route.md` reduces this to singleton counts
(7,7,8,8), no exact triple members, all root degrees15, and the following
four pair-count profiles in order01,02,03,12,13,23:

| Name | Pair counts |
|---|---|
|A|(1,3,3,3,3,0)|
|B|(2,2,3,3,2,1)|
|C|(3,1,3,3,1,2)|
|D|(3,2,2,2,2,2)|

At a low root i in {0,1}, the actual link triple A_i=R minus i has exactly
seven disjoint companions, and the complete point-link has size15.
The three degrees of points j in A_i within that link are exactly

    d_(L_i)(j)=d_F(i,j)=1+p_ij<=4,                       (1)

because no exact root triples occur. In particular rho(L_i)>=7.

## If rho is eight, the precise shared-leaf form is forced

Suppose rho(L_i)>=8. The universal exact-singleton bound gives equality8.
Choose an actual triple B with eight disjoint companions H. B4 makes
K=N_(L_i)[B] intersecting, so the complete link is H union K of sizes8+7.

Every actual triple of a two-cover P8 or Q8 contains a point of degree5
inside that size8 family: the two-cover points of P8 have degree5, and
every Q8 triple contains a hub. Consequently A_i cannot lie in H, by
(1); it lies in K.

If H is P8, isolation makes K avoid its entire support. The deleted-block
exceptions are on supp(H), which is disjoint from B; an actual exception
would therefore belong to H rather than K. But A_i would then have all
eight H triples disjoint, contrary to its known count7. Thus H is Q8,
say Q(h,k;U;l,m).

The same far-side isolation argument makes K avoid H's entire five-point
core {h,k} union U: each exceptional hub-plus-both-leaves triple is on
supp(H), avoids B, and cannot belong to K. Only the two leaves may occur
in K. Since K is intersecting and A_i has seven disjoint triples in H,
A_i contains exactly one leaf, say l. Indeed each leaf belongs to exactly
one H block, so containing neither, one, or both would give8,7,6 disjoint
H blocks respectively. Write l=j, one of the other root points.

Relative to A_i, the near family is now precisely K plus {j,h,k}.
Restoring i, that extra member is {i,j,h,k}, an exact pair member of
category ij. All other members of this category come from K and avoid
h,k. But all exterior edges of one exact pair category must intersect:
two disjoint such edges and R would form a sunflower with core {i,j}.
Therefore no other member occurs in that category, and

    p_ij=1.                                             (2)

The two other pair categories have total size6 and individual cap3, so
both have size3. Their exterior edges are triangles. Since they are
members of the intersecting K with different root partners, every edge
of either triangle meets every edge of the other. A two-set covering a
triangle is one of its edges, so the two triangles coincide; call it T.
The Q8 core is disjoint from K, hence

    the exceptional edge {h,k} is disjoint from T.        (3)

We have proved a necessary literal form for every rho8 alternative at a
low root: its pair row must be(1,3,3), the p1 edge is off the common
triangle of the two p3 categories, and it consists of the two far Q8 hubs.
No classification of an arbitrary intersecting I7 was used.

## Consequences for profiles B,C,D

The low-root rows in B are permutations of(2,2,3), and those in D are
permutations of(3,2,2). They contain no p1 category, contradicting (2).
Thus both low-root links in B and D have rho=7.

In C both high roots2,3 have singleton8 and pair row6. Their pair residues
lie on triangles T_2,T_3 by the ordinary B4 triangle lemma. The category23
has size2, so these triangles coincide, say T. At low root0 the possible
exception has category02 of size1; the size3 category03 already has the
triangle T. The exception lemma would put the category02 edge outside T.
But that edge is also incident with high root2, so it lies on T. This is
impossible. The same argument at low root1 uses its singleton category13.
Hence both low-root links in C also have rho=7.

## In profile A the two exceptions cannot occur together

If both low-root links had rho8, their exceptional category would be01.
Let its unique actual four-set be E={0,1,a,b}. At root0 the exceptional
Q8 hubs are a,b, and its two leaf triples supply E and another actual
member {0,a,b,m_0}, where m_0 is different from1. The other component
avoids a,b. Thus

    d_F(0,a)=d_F(0,b)=5,     d_F(0,a,b)=2.

The analogous statements at root1 give pair degrees5 and triple degree2
there as well. Since T=0 and p01=1 at the original root,

    d_F(0,1)=2,
    d_F(0,1,a)=d_F(0,1,b)=1.

Finally d_F(a,b)>=3, because E, {0,a,b,m_0}, and {1,a,b,m_1} are three
distinct actual members. The second lacks1 and the third lacks0.

Apply exact inclusion-exclusion to the neighbourhood of the actual E:

    N(E)=sum_(v in E)d(v)
         -sum_(pairs in E)d(pair)+sum_(triples in E)d(triple)-1
        <=60-(2+5+5+5+5+3)+(1+1+2+2)-1
        =40.

This contradicts mu>=41. Therefore at least one low-root link in A has
rho=7. Combining the cases, every N44 anchor supplies an actual
15-member SF3 link with rho=7, whose distinguished actual triple has
point-degree multiset either (2,4,4) or(3,3,4).

## Conditional closure using the new R15 classification

The separate current theorem being supplied by local_arithmetic is:
every15-member SF3 family with rho=7 is R16 with one triple deleted.
This assertion is an explicit prerequisite for the following paragraph;
the reduction above does not assume it or resolve rho<=6 families.

In the universal R16 template, four hubs have degree6 and six triad points
have degree4. There are two deletion types. Deleting a hub triple leaves
three hubs of degree5 and the fourth of degree6; all triad degrees remain4.
Deleting a hub-plus-triad-edge triple lowers that hub to5 and precisely
the two edge endpoints to3; the other hubs remain6 and other triad points4.
Thus every used point still has degree at least3, excluding a distinguished
triple of degree pattern(2,4,4).

A pattern(3,3,4) is also impossible. Its two degree3 points would have to
be exactly the endpoints of the deleted triad edge. Before deletion they
occur together only with the two hubs assigned to that triad. One of these
two triples was deleted; the remaining triple has the other hub as its
third point, and that hub has degree6. It cannot have degree4.

Consequently, conditional on the separate rho7 classification, every N44
anchor is excluded and every actual neighbourhood is at most43 under
cap15. The unresolved rho<=6 link domain is not needed for this deduction:
the displayed anchor has exactly seven disjoint companions. This is a
conditional ordinary NO44 result, not a proof excluding the entire cap15
branch or a completed Lean theorem.
