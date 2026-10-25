# Independent check of P9 complement rigidity, NO45 and the cap15 no-P9 consequence

23 October 2026. Bounded ordinary proof development. This is a separate
check of `LOW15-two-low-core.md`, not a final research audit, a new replay
of imported certificates, or a Lean formalization. No LP, Lean process,
geometric enumeration or exterior-support bound was used.

The repaired argument is valid under its stated imported premises. It
proves N(R)<=44 for every actual member of a hypothetical68-member SF4
family with global point-degree cap15. A further consequence, proved below,
is that no point-link contains P9 in this domain, hence all exact singleton
counts are at most8. Neither statement alone excludes the cap15 branch.

## Premises and dependency order

F is finite, simple and four-uniform, and has no three-member sunflower,
including empty core. Assume |F|=68 and Delta<=15. H27 gives mu>=41.
The imported facts are P8/Q8/P9/P10 classification and isolation, B4,
global triple-codegree cap2, the canonical P9 transversal facts, crowding26,
and HP15 in its proved mu>=41,Delta<=18 actual-star scope.

The order is important and contains no circular no-P9 assumption:

1. The preceding P10 cone-average argument excludes P10 subfamilies in all
   point-links at cap15, giving singleton cap9.
2. Crowding gives S<=34. The degree identity gives N<=46. The established
   common-triangle/HP15 argument excludes N46 and gives N<=45.
3. Under N<=45, the complement estimate below forces any P9 component's
   residual link to be a six-triple common-point family.
4. An N45 anchor is incompatible with that rigid residual link, giving
   N<=44.
5. Only after this improvement do we exclude every P9 component, including
   its six-triple common-point alternative.

Steps1--2 are in `LOW15-mu41-research.md` and
`LOW15-large-singleton-core.md`. The scalar179 and cone-incidence count in
step1 were independently checked earlier in `LOW15-count-check.md`.

## Completeness is preserved in the complement

Suppose L_x contains H=P9 on its six-point support W. P9 isolation says
every other link triple is either its missing P10 block or disjoint from
W. The missing block is absent by the already proved no-P10 result. Thus

    L_x = H disjoint-union K,     |K|<=15-9=6,

and every triple in K avoids W. This is the complete point-link in F.

Let Q be an actual member disjoint from {x} union W, and set I=D(Q), the
actual members disjoint from Q. This family is intersecting, since two
disjoint members of I together with Q would be an empty-core sunflower.
All nine H-cones lie in I. Its complete x-link is exactly H union K',
where K' is the subset of K whose cones avoid Q. Nothing asserts that K'
is absent. Write k=|K'|.

For k=0, the complete-P9 bound in the frozen paper gives |I|<=20. That
bound includes four-sets internal to W. This is the only case in which
the original complete-P9 bound is applied directly.

For k>0, an x-avoiding member of I must meet every H-cone, so its W trace
is a cover of H and has size at least3. It must also meet every x-cone
from K', whose tails avoid W. Therefore it has exactly three W points
and one point outside W, and the latter lies in the intersection of K'.
In particular no W-internal four-set is possible in this case.

## Counting the block and exceptional traces separately

Write H=P10 minus B. Its three-point transversals are the nine blocks of
H, together with B and C=W minus B. Every H block has at most one remaining
occurrence in an x-avoiding member, after subtracting its prescribed x-cone
from global triple-codegree2. Their contribution is therefore at most9.

The exceptional traces B,C contribute at most2 together. If just one
occurs, its triple capacity is2. If both occur, their W parts are disjoint,
so intersection of I forces every exterior point from the B class to equal
every exterior point from the C class. Simplicity then leaves at most one
member in each class. This also handles arbitrary exterior support.

Consequently, for every k>0,

    |I| <= (9+k)+9+2 =20+k.

For k=1 or2 this gives at most22.

## The actual HP15 guard for k>=3

The common intersection of K' has at most one point: if two points z,z'
belonged to three distinct K' triples, the three corresponding actual
x-cones would all contain the triple {x,z,z'}, violating codegree2.
If the common intersection is empty, there are no x-avoiders in I and
|I|=9+k<=15.

Otherwise its unique point is z. Every x-avoider in I is {z} union T,
for one of the eleven transversal triples T. Let J be the subfamily of
such tails T which are blocks of H. The following guards are all literal:

* J is a subfamily of H, so it is intersecting and SF3;
* H is intersecting, so H and J are cross-intersecting;
* the distinct centres x,z lie outside W and therefore outside both tail
  supports (z belongs to K', whose triples avoid W and x);
* every x-cone over H and z-cone over J is an actual member of F.

If |J|>=7, these stars have total size at least16, contrary to the imported
cross-star theorem and mu>=41,Delta<=18. Thus |J|<=6. The two exceptional
transversal classes are not put into J and still contribute at most2.
This yields

    |I| <=9+k+6+2 =17+k       (k>=3).

There is no assertion that all eleven transversal triples form an
intersecting triple family. Separating the two exceptions is essential.

If max point-degree in K is at most5, then k<=5 whenever K' has a common
point, so every case gives |I|<=22. Without this hypothesis, |K|<=6 still
gives the uniform bound |I|<=23.

## The exact-one-W pool and its incidence contradiction

Under N<=45, an actual Q as above would have |D(Q)|>=23. Therefore when
max degree(K)<=5 the preceding bound excludes every such Q. All members
avoiding x must then meet W.

Let n=68-d(x)>=53. Let H_W count only the members avoiding x whose exact
trace on W has size1. **It is this subfamily that is intersecting.** The
argument does not claim all n members avoiding x are intersecting.

If two members of the exact-one-W subfamily were disjoint, their at most
two W points are avoided by a P9 block. Such a block exists because each
pair of points is avoided by two P10 blocks and deleting one leaves at
least one. Its actual x-cone is disjoint from both members: they avoid x
and have no other W points. This would be an empty-core sunflower. H27
therefore gives H_W<=27.

The total W incidence of the n members avoiding x satisfies

    D_W <= sum_(w in W) d(w) -27 <=6*15-27=63.

The nine prescribed x-cones contribute exactly27 incidences, and K avoids
W. Every one of the n members has at least one W point; all except the
H_W exact singletons have at least two. Thus

    106 <=2n <=D_W+H_W <=63+27=90,

a contradiction. Internal W four-sets and larger W traces only strengthen
the middle incidence inequality. No finite exterior universe is assumed.

It follows that a P9 component under N<=45 must have K of size6 and a
point occurring in all six triples. Indeed, every other K of size at most6
has maximum point-degree at most5. This is precisely the residual case
left by the repaired argument, not a premature no-P9 conclusion.

## Checking the direct NO45 step

At an actual N45 anchor, the degree identity is

    sum_i d(i)=92-S+T<=60.

Together with S<=34 and s_i<=9, this gives S>=32+T and T<=2. If no
singleton is9, then every singleton is8, T=0 and all degrees are15;
all pair-rows are6, so the previously proved common-triangle theorem
already excludes this case.

Otherwise choose x with singleton9. Its exact singleton tails form P9,
and the rest of its complete link is exactly the near family K. Isolation
separates their supports. Rigidity gives |K|=6 and a common point z. Since
R minus x is one of those near triples, z is one of the other root points.

Every near member through x contains z. Such members consist of R, the
exact pair category xz of size at most3, and the two possible exact triple
categories containing x,z, each of size at most1. Their total can reach6
only if all three bounds are equalities. Thus p_xz=3 and both relevant
triple categories occur, giving T>=2. The earlier inequalities now force

    T=2, S=34, all degrees15, sorted s=(8,8,9,9).

The two triple types omit the two roots other than x,z. At least one of
these omitted roots l has singleton8, since x already uses one of the two
singleton9 positions. For this root t_l=1 and

    r_l=15-1-8-2+1=5.

But the literal triple member omitting l, together with the other three
singleton counts at least8, forces every incident pair residue at l to
contain its exterior point u. Removing l,u gives a simple bipartite graph
of maximum degree2, by triple codegree, and matching number at most2, by
sunflower-freeness. Its components are paths and even cycles, so it has
at most4 edges. Hence r_l<=4, the required contradiction.

This proves N<=44 under the stated cap15 premises without relying on
the finite N45 profile census or its individual case closures.

## The stronger consequence after NO45

Now suppose any point-link contains P9. Isolation and no-P10 still give
the complete decomposition H union K with |K|<=6. An actual Q outside
{x} union W would have |D(Q)|=68-N(Q)>=24, since N<=44 has just been
established. The complement bounds above give at most20 for k0, at most22
for k1/2, and at most23 for k>=3. Thus no such Q exists, including when
K is the six-triple common-point family.

Every member avoiding x therefore meets W, and the same exact-one-W
pool/incidence contradiction106<=90 applies. There is consequently no
P9 subfamily in any point-link at cap15. Exact singleton families of size
at least9 contain P9 by the I9 classification, so every exact singleton
count is at most8.

The conclusion is conditional on the named imported ordinary and certified
facts. It does not establish the global upper bound67, exclude every
Delta15 family, or turn the earlier component/certificate work into a
single checked Lean theorem.

## Source locators and boundary

The frozen prior repository is
`work/frontier20261020/prior-art68/repository`. In `paper/main.tex`,
lines188--331 give the canonical families, isolation and B4; lines333--372
give the universal caps and exact trace identities; lines968--1024 give
crowding and the actual cross-star guard; lines1124--1144 give the complete
P9/P10 intersecting-family bound20. The present check reuses those stated
facts and the already recorded selected replay provenance. It does not
reconstruct the full external certificate chain or the imported H27 proof.
