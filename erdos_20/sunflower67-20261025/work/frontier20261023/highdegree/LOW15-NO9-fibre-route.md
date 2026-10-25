# Cap15 NO9 and the remaining fibre problem

23 October 2026. Ordinary research following the new NO45 argument.
This is a separate downstream note; no old mu42 interface is imported.
No LP, Lean, or new fibre enumeration is performed here.

## No P9 remains after NO45

Assume the premises and conclusions of `LOW15-two-low-core.md`: F is
SF4 of size68, Delta<=15, no P10 occurs in any point-link, and every
actual neighbourhood has size at most44. H27, P9 isolation, and HP15
are the named imported inputs.

Suppose a complete point-link contains a P9 component H on W. By P9
isolation and no P10, its remaining subfamily K avoids W and has size
at most6. For an actual Q outside the seven-point star support, the
intersecting complement I=D(Q) now has size at least24. Its complete
point-link is P9 plus K', k=|K'|<=6. The exact complement bounds proved
in the preceding note give:

* k=0: |I|<=20;
* k=1,2: |I|<=20+k<=22;
* k>=3: if K' has no common point, |I|<=15; otherwise
  |I|<=17+k<=23, using HP15 only on its P9-block portion.

All possibilities contradict |I|>=24, including the six-triple
common-point exception left by the earlier N<=45 argument. Hence
every member avoiding the star centre meets W. The exact-one-W
subfamily is intersecting by the prescribed-cone witness, so H27
bounds it by27. The other members need only meet W; they are not
asserted to form an intersecting family. As before their W incidence
is at most63, whereas there are at least53 such members. Thus
106<=63+27, a contradiction.

Consequently no P9 subfamily occurs in any point-link under cap15.
In particular every exact singleton at every actual anchor is at
most8, by the intersecting I9/I10 classification. The proof is acyclic:
no P10 -> NO46 -> NO45 -> no P9. NO45 did not assume this new no-P9
conclusion.

## Exact graph domain supplied by the new conclusions

The disjointness graph G has68 vertices, is triangle-free, has
alpha(G)<=27 by H27, and minimum degree at least24 from N<=44.
Jin's imported theorem applies with k=6 since

    24*20=480 > 7*68=476.

The k=5 test is equality, 24*17=6*68, and cannot be used. With the
cyclic convention on Z/(3k-1), A_k has edges at differences
k,...,2k-1. Deleting empty fibres by the ordinary map

    f(v)=v-1-[v>=k]-[v>=2k],  1<=v<=3k-2,

reduces to a surjective image with k in {1,...,6}. For an edge of
ordinary difference d in [k,2k-1], this map subtracts the number of
the two thresholds k,2k crossed; the resulting difference is in
[k-1,2k-3]. Rotation handles any deleted vertex. A1 and A2 are
excluded by respectively 68<=2*27 and 2*68<=5*27. Thus k=3,4,5,6.

Let a_i be the nonzero fibre masses and
b_i=sum_(j adjacent i) a_j. Each union of adjacent fibres is an
independent set, while a vertex in fibre i has all neighbours there.
Therefore 24<=b_i<=27. Put r_i=b_i-24. The cyclic incidence identity
gives the exact arithmetic domain

    r_i in {0,1,2,3},
    sum r_i =24-4k,
    a_i=4+r_i+r_(i+k)+r_(i+2k-1).

All subscripts are modulo3k-1. To verify the inverse identity, expand
b_i+b_(i+k)+b_(i+2k-1): every fibre mass occurs once, and a_i once
more, so the sum equals68+a_i. Summing the b_i gives68k and yields
the r sum above. In the A6 case all r_i vanish and all seventeen
fibre masses equal4.

These are the same order68 graph formulas derived in
`work/frontier20261020/prior-art68/analysis/prior68-research.md`.
Their current validity follows from the newly proved cap15 reductions;
it does not import that note's additional maximum-degree16 hypothesis.

## Star constraints and independent supports

For any actual point x of degree m, let t_i count its members in fibre i
and q_i=sum_(j adjacent i) t_j. Then

    sum t_i=m, 0<=t_i<=a_i,
    q_i<=r_i whenever t_i>0.

Indeed an actual star member in fibre i is nonadjacent to every other
star member, including the q_i members in adjacent fibres. Its graph
degree is therefore at most b_i-q_i, but is at least24. No assertion
that every permitted inter-fibre edge is present is needed.

If the support of t is independent in A_k, it lies in a cyclic window
of k consecutive indices. Here is an ordinary proof, avoiding a finite
support catalogue. Rotate one occupied index to0. Every other occupied
index is between1 and k-1 or between2k and3k-2. If both groups occur,
let a be the largest positive index and let -b be the most negative,
with 1<=a,b<=k-1. The nonedge condition between a and -b forces
a+b<=k-1: their ordinary difference is3k-1-a-b, which is larger
than k and hence must exceed2k-1. All occupied indices then lie in
the window [-b,a]. If only one group occurs the window is immediate.

Every such window is the neighbourhood of an image vertex and has
total mass at least24. Each member in this window outside the x-star
meets every star member, since a graph homomorphism cannot map an
edge into a nonedge. Thus it is an actual four-point transversal of
the complete link L_x. There are at least24-m such transversals.

## A useful ordinary full-transversal bound for a separated 8+7 link

Suppose m=15 and L_x has some triple A with eight disjoint triples.
The disjoint subfamily H has size8 and is intersecting, because three
disjoint link triples would be a sunflower. Its complement K has
size7 and is intersecting by B4. Thus H is P8 or Q8 and K is an
arbitrary intersecting SF3 family of size7. No I7 catalogue is
required below. K has transversal number at least2: a common point
would give an SF2 point-link of size7, exceeding the universal bound6.

If H is P8, isolation separates its entire support from K. A
four-point cover of L_x therefore has exactly two points covering H
and two covering K. If H has no two-cover, there is no four-cover.
Otherwise its two-cover is unique. To see this, a P10 pair is avoided
by exactly two blocks, and it covers the P8 exactly when these are
the two deleted blocks. Those two blocks have a four-point union,
whose complement uniquely determines the cover pair. This pair is
contained in two prescribed H blocks, neither of them deleted.

If H=Q(h,k;U;a,b), isolation puts its five-point core {h,k} union U
outside the entire support of K; only its leaves a,b may overlap K.
Any four-cover containing precisely one hub needs at least two U
points to meet the opposite hub's three core triples, leaving only
one point for K, impossible. A four-cover with neither hub must
contain both leaves and at least two U points. It would therefore
require {a,b} to cover K. But each leaf has degree at most3 in K:
two K triples through a with disjoint residual pairs, together with
the H triple {h,k,a}, would form a sunflower. Its residual pairs
are thus intersecting SF2 and have size at most3. The same holds
for b, so their union meets at most6 K triples, fewer than7.

Thus every four-cover in the Q8 case contains the hub pair {h,k}.
That pair belongs to the two prescribed leaf blocks of H. In either
nonempty-cover case, every actual four-transversal avoiding x
contains one fixed pair, and two existing x-cones already contain
that pair. The global pair codegree bound6 therefore leaves room
for at most4 actual four-transversals.

Consequently a degree15 star with such an 8+7 link cannot have an
independent fibre support: the window argument would supply at
least24-15=9 actual four-transversals, exceeding4.

## What this does and does not settle

The previous ordinary cap14 exclusion means that a remaining cap15
family has an actual degree15 point. All its links have at most
eight triples disjoint from any member, by the new singleton bound.
If a degree15 link attains eight, the separated8+7 argument above
applies. Otherwise it has at most seven disjoint triples per member;
call this the size15 analogue of the R16 domain, without claiming
the R16 theorem applies to it.

In the A6 image, r=0 forces every point-star to have independent
support. Therefore every degree15 link in that case must lie in
this at-most-seven-disjoint-triples domain. For A3,A4,A5 the missing-
star-edge constraints permit nonindependent star supports; their
deletion-transversal requirements remain to be studied for size15.

The old order68 terminal census is for a degree16 star and separated
8+8 links, with cover capacities after deleting up to three triples.
It cannot be reused merely by changing16 to15. The new conclusions
restore the singleton<=8 and N<=44 interfaces at cap15, but do not
create a degree16 point or exclude the size15 small-disjointness
domain. That is the remaining ordinary structural gap in this
fibre route. No global cap15 exclusion is claimed here.
