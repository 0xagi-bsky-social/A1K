# Full and one-deletion transversals of the remaining degree16 links

23 October 2026. Ordinary development on arbitrary exterior support; no
enumeration, LP, or Lean run. This note supplies a graph interface, not a
closure of the degree16 or global67 problem.

## Current ordinary domain

Let F be a finite simple SF4 family of size68, including the prohibition
on empty-core sunflowers, with Delta<=16. Use the preceding ordinary
no-P10, global no-P9, NO46 and NO45 results, H27, B4 and isolation. Thus
every exact singleton is at most8 and every actual N(Q)<=44. The prior
universal R16 theorem and its separate cap61 exclusion leave a degree16
point x with a complete link partitioned into two intersecting families
of size8. P8 whose deleted P10 blocks intersect in one point has separately
been excluded by `D16-P8-no-two-cover-exclusion.md` when that note's
premises are invoked. Equivalently, the geometric statements here assume
the two components are the remaining two-cover P8 or Q8 types.

If a component is P8, isolation separates its entire six-point support
from the opposite component. If both are Q8, their five-point cores avoid
the entire opposite support, and only their two leaves may be shared.
This is the reciprocal-core argument in `D16-NO47-ordinary.md`; full
seven-point support separation is not assumed for Q8.

Write

    P*=P10 minus {012,015}
      ={023,034,045,124,134,135,235,245}.

Its unique two-cover is {3,4}. Every two-cover P8 is equivalent to this
one under a P10 automorphism, or the same argument can be stated for the
two omitted blocks B,C: the unique cover is W minus (B union C).
For Q(h,k;U;l,m), where U has three points, its unique two-cover is {h,k}.
All points in each displayed Q8 are distinct; shared leaves refer only
to the two different components.

## The full four-transversal is unique

If a P8 component occurs, disjoint support and transversal number2 on
each component force a four-cover to use exactly two points in each
component support. Both pairs must be the unique two-covers. No outside
point can appear.

For Q8/Q8 let C_1,C_2 be their disjoint five-point cores. The six core-only
triples of each Q8 have no one-point cover, so any full cover uses at
least two points in each C_i. Four available positions are exhausted:
exactly two points lie in each core and no leaf is used. To meet the
two leaf triples of the first component, its core pair must contain a
hub. If it contained precisely one hub and one triad point, it would
miss the other hub with the opposite triad pair. Thus it contains both
hubs. The same holds in the second component. Shared leaves cannot
alter this argument because neither leaf is selected.

In all cases the unique four-transversal is the union of the two unique
two-covers. This is an exact four-set; simplicity permits at most one
actual x-avoider meeting all16 x-cones.

## A prescribed omitted triple has at most one quasi-transversal

A quasi-transversal relative to A in L_x is a four-set disjoint from A
and meeting every other link triple. The remaining seven triples in a
component still have no one-point cover: their maximum point degree is
at most5. Thus in the P8-containing cases exactly two positions are
needed in each disjoint component support. In the Q8/Q8 cases, deleting
one core-only triple leaves five core-only triples with no one-point
cover, so the same two-core-point argument works. Deleting a leaf triple
leaves all six core-only triples. No outside point can occur in any case.

For P*, the possible two-covers of P* minus A which avoid A are exactly
the following. The other four rows have no such pair.

| A | Required pair |
|---|---|
|023|45|
|045|23|
|124|35|
|135|24|

This table has a direct two-omission proof. Every pair of the six-point
P10 support is avoided by exactly two P10 blocks. To cover P* minus A,
these two blocks must lie among {012,015,A}. The pair associated with
{012,015} is the original two-cover34, which meets every actual A and
therefore cannot be a quasi-cover. The other possibilities are the
complements of A union012 or A union015 when those unions have size4.
Inspection of the eight displayed blocks gives exactly the four rows.
In particular two distinct quasi-covers never occur for the same A.

For Q(h,k;{u,v,w};l,m), a core-only omitted triple A={h,u,v} has the
unique quasi-cover {k,w}; interchange the two hubs or the triad labels
for the other five cases. It avoids A, meets the two leaf triples via k,
and meets the remaining h-triples via w. To prove uniqueness, a cover
with two core points cannot avoid A except by choosing those two points.
For a leaf triple A={h,k,l}, avoiding both hubs forces two triad points
to cover the six core-only triples, leaving the other leaf triple
{h,k,m} uncovered. Hence a leaf triple has no quasi-cover.

Combining the local pair with the unique two-cover of the other component
proves the result. In Q8/Q8 the other hub pair avoids A even when leaves
are shared, since opposite cores avoid the whole first support.
Thus the number of A admitting a quasi-transversal is8 for P*/P*,10
for P*/Q8, and12 for Q8/Q8, independently of shared-leaf count. These
counts follow from the explicit ordinary formulas, not a new80-case run.

## Consequences for the current order68 fibre domain

The disjointness graph has minimum degree24 and independence number at
most27. In the current Jin/Andrasfai fibre interface, write a_i for
nonempty fibre masses, b_i for the mass in adjacent fibres, and
r_i=b_i-24. Thus 24<=b_i<=27. For a degree16 point-star, let t_i count
its members in fibre i, I={i:t_i>0}, and q_i=sum_(j adjacent i)t_j.
The absent-edge budget gives q_i<=r_i whenever t_i>0.

If I is independent, it lies in a cyclic window of k consecutive image
indices, as proved in `LOW15-NO9-fibre-route.md`. That window has mass
at least24. Every member in it meets every star member: a disjoint pair
would map to an edge inside the independent window, impossible. The
window therefore contains at least24-16=8 actual full transversals,
contrary to uniqueness. Every degree16 star has nonindependent fibre
support. In the A6 image r is identically zero, forcing independent
support, so A6 is impossible whenever a degree16 point exists.

More generally let J be the set of image indices nonadjacent to every
occupied star index. Every x-avoider in those fibres is a full
transversal, so

    sum_(i in J) (a_i-t_i) <=1.

If q_i=1, every x-avoider in fibre i meets the other15 prescribed star
members. It either meets the remaining member, becoming the unique full
transversal, or avoids it, becoming its unique possible quasi-transversal.
Thus a_i-t_i<=2. If the unique full transversal is already supplied by
J, an index outside J with q_i=1 has a_i-t_i<=1. More strongly, all
fibres whose sole adjacent star member is the same actual cone share
one quasi-transversal capacity; that capacity is not renewed per fibre.

For q_i=2 or3, a complete deletion-cover bound is still required. The
preceding claims do not substitute the one-deletion formula for those
cases, and do not assert that all admissible inter-fibre edges occur.
The remaining A3/A4/A5 analysis and its finite arithmetic checks are
separate downstream work.
