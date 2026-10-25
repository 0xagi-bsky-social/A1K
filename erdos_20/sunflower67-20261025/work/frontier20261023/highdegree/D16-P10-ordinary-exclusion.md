# Ordinary exclusion of P10 in a point-link at global cap16

23 October 2026. New ordinary proof development, not a final audit, numerical
certificate replay, or Lean formalization. No solver, support enumeration or
Lean process was used. All exterior points remain unrestricted.

**Claim.** Under the imported facts stated below, a simple SF4 family F
of68 members with global point-degree cap16 has no P10 subfamily in any
point-link. Consequently every exact singleton family has size at most9.
This excludes the P10+I6 alternative for a complete degree16 link; it does
not by itself exclude all degree16 or degree17 links.

## Premises and prior ordinary lemmas

F has no three distinct members with all pairwise intersections equal,
including empty core. H27 gives mu>=41. We use the universal SF3 degree
and I8/I9/I10 facts, isolation, B4, triple-codegree2, crowding26 and its
imported actual-star provenance. Two ordinary lemmas are used explicitly:

1. An intersecting SF4 family whose complete point-link is P10 has size
   at most20, including internal four-sets. This is the ordinary capacity
   argument in the frozen paper, lines1124--1144.
2. A complete C5 point-star in an SF3 family of size at least16 belongs
   to an intersecting component of size5+I, where I counts internal
   C5-cover triples; the other component has size at most10. In particular
   absence of all such internal triples forces total size at most15.
   `C5-internal-compatibility.md` proves this with the R16 exception and
   the possible shared Q8 leaves addressed explicitly.

The second lemma requires a complete C5 point-link, not merely five
prescribed triples. Completeness is checked below. Its R16 classification
input is conditional on the pinned prior theorem; no new classification
replay is claimed here.

## Every actual neighbourhood has size at most47

For an actual anchor let S,P,T be its exact singleton, pair and triple
count sums. Then

    N=1+S+P+T,
    sum d_i=2N+2-S+T.

Crowding26 bounds the three largest singletons by26. The smallest is at
most8, so S<=34. Global cap16 gives N<=48. Equality N48 forces T0,S34
and all four degrees16. The singleton cap10 leaves just

    (8,8,8,10) or (8,8,9,9).

Whenever a singleton count is at least8, B4 implies that its pair-row
is at most6, regardless of T. If every incident category is at most2
this is immediate. Otherwise a category of size3 is an exterior triangle;
every other incident edge must cover it and hence be one of its edges.
Each of the three edges has multiplicity at most2 by triple codegree.

At either N48 pattern a singleton8 point has pair-row7, a contradiction.
Thus every actual Q has

    N(Q)<=47,             |D(Q)|=68-N(Q)>=21.                (1)

This preliminary step does not assume that P10 is absent.

## A P10 component forces a nonempty outside pool

Suppose L_x contains H=P10 on a six-point support Y. Put m=d(x)<=16.
P10 isolation gives the complete decomposition

    L_x=H union K,       |K|=m-10<=6,

where every triple of K avoids Y. If needed, K is intersecting: two
disjoint K triples together with any H block would be three disjoint
triples in L_x. No classification of an arbitrary I6 is required.

Consider all n=68-m residual members avoiding x. Let O,H_1,P_2,E_3,I_4
count those whose exact Y traces have sizes0,1,2,3,4. These five quantities
count actual members, including arbitrary exterior completions. Write

    D_Y=H_1+2P_2+3E_3+4I_4.

The union of the trace0 and trace1 classes is intersecting. If two such
members were disjoint, their Y traces would have union of size at most2.
A P10 block avoids that union, so its actual x-cone would be disjoint
from both, giving an empty-core sunflower. H27 therefore gives

    O+H_1<=27.                                             (2)

Initially the global cap16 gives

    D_Y<=6*16-30=66,

subtracting the30 incidences of the ten prescribed x-cones. K contributes
none on Y. Since

    2n=D_Y+H_1+2O-E_3-2I_4 <=66+27+O,

and n>=52, we obtain O>=11. In particular an actual Q disjoint from
{x} union Y exists. This conclusion includes internal and nonblock triple
traces; neither has been discarded at this stage.

## Every internal Y four-set is absent

Choose any such outside Q and let A=D(Q). It is an intersecting SF4
family, because two disjoint members in A together with Q would form
an empty-core sunflower. Its complete x-link is H union K', where K'
is exactly the subset of K whose x-cones avoid Q.

If K' were empty, the complete-P10 bound20 would give |A|<=20, contrary
to (1). Thus some actual x-cone {x} union U, U in K, is disjoint from Q.

An actual four-set B contained in Y would be disjoint from both Q and
{x} union U. These latter two are also disjoint. The three distinct actual
members would form an empty-core sunflower. Hence

    I_4=0.                                                 (3)

The complete-link bound20 was used only after proving its complete-link
guard in the hypothetical K'=empty case. Additional outside link triples
were retained in all other cases.

## All six P10 support points have degree at most15

Fix y in Y. In the complete link L_y, the point x has exactly the five
triples corresponding to the point-y C5 in P10. There cannot be another
triple through x: every remaining triple in the complete L_x lies in K
and avoids Y. Thus the C5 point-link is complete.

If d(y)>=16, the complete-C5 structural lemma applies. Its component
containing x contains the five C5 cones, and every additional member of
that component is a three-vertex cover of the cycle on Y minus y. Such
a triple would lift to an actual four-set contained in Y, contrary to
(3). The component would have size5 and its disjoint opposite component
at most10, contradicting total size at least16. Therefore d(y)<=15.
Summing over the six support points gives the improved incidence cap

    D_Y<=6*15-30=60.                                       (4)

The explicit R16 check behind this lemma is that its point degrees are
only4 or6, never5. In the remaining Q8/Q8 alternative, a point with a
complete C5 link cannot be a hub or triad point (triangle/C4 sublinks),
and a possibly shared leaf has total degree at most2. Thus no assumption
of disjoint Q8 leaves is hidden in (4).

## Cone average contradicts the trace count

Let W be the sum, over the ten prescribed x-cones, of the number of
residual members meeting that cone. Every member containing x meets
every cone, so mu>=41 gives

    W=sum_(A in H)(N[x union A]-m)>=10(41-m).                (5)

A singleton Y trace meets exactly5 P10 blocks, and a pair meets exactly8.
A triple meets at most10. Using I_4=0, therefore,

    W<=5H_1+8P_2+10E_3
      =5D_Y-2P_2-5E_3.                                   (6)

This upper bound permits every nonblock triple trace; it does not require
that all global triple traces be P10 transversals.

From n=O+H_1+P_2+E_3 and (2),

    P_2+E_3>=n-27=41-m.                                  (7)

Combining (4),(6),(7) gives

    W<=300-2(P_2+E_3)-3E_3
      <=218+2m-3E_3.

Together with (5),

    410-10m<=218+2m-3E_3,
    64<=4m-E_3.

As m<=16 and E_3>=0, equality is forced: m=16 and E_3=0.

But choose an actual Q in the nonempty outside pool. By (1), D(Q) has
at least21 members, while at most16 contain x. Thus at least5 members
of D(Q) avoid x. Each must meet all ten prescribed x-cones, since D(Q)
is intersecting, so its Y trace has size at least3. Internal four-sets
have already been excluded, so all these members have exact Y trace
size3. Therefore E_3>=5, a contradiction.

This completes the ordinary no-P10 proof at global cap16.

## Consequence for the degree16 link reduction

The prior R61 theorem already rules out a complete R16 link at cardinality68
in its mu>=41,Delta<=18 scope. This is a separate imported source result,
not a consequence of the cone average above. For any remaining complete
link of size16, some actual triple has at least8 disjoint triples, and
B4 gives two intersecting parts of sizes10+6,9+7 or8+8.

The present proof removes10+6. The alternatives left are P9+I7 on disjoint
supports, or two I8 parts. A P-type I8 has whole-support isolation; for
two Q8 parts only the cores are isolated and up to two leaves may be shared.
No unproved I7 finite classification or full Q8-support separation is used.
This is the next ordinary reduction boundary, pending further no-P9 or
eight-part arguments.

## Source boundary

Frozen prior repository:
`work/frontier20261020/prior-art68/repository`.
In `paper/main.tex`, lines188--331 give the canonical families, isolation
and B4;333--350 give universal caps;443--462 state the R16 classification;
968--1024 give crowding/cross-star;1124--1144 give the complete-link
intersecting bound20. The complete-C5 support argument is written in
`C5-internal-compatibility.md`, including its precise source locators.

Only these named ordinary/imported results are composed here. The old
mu42 bootstrap, size69 branch exclusions, and old support/minimum-degree
assumptions are not premises. No end-to-end Lean or global67 conclusion
is asserted.
