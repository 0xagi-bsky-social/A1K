# Closing the degree-twenty branch below 68

Working mathematical note, 23 October 2026. Final reviews and publication remain
closed. This gives an ordinary computer-assisted proof with explicit imported
universal structure; it is not an end-to-end Lean theorem or a global bound67.

## The precise branch theorem

Assume the universal SF3 bound20 and its high-link classifications, the
intersecting SF3 capacities and B4 separation, the universal separated-C5
obstruction, and the intersecting SF4 bound H27, as stated in the pinned
upper-68 source. Every finite simple four-uniform three-sunflower-free family
with a point of degree20 has at most67 members. Empty cores are forbidden.
No ground-set size restriction, positive minimum degree, or mu42 hypothesis
is imposed. H27 enters only the final disjointness double count below.

Normalize the degree20 link to the two P10 components Y,Z in
`internal-proof.md`. If the family contains an internal member, that note
already gives |F|<=67. Thus, for a putative |F|>=68, both components contain
no internal four-member. The universal C5 obstruction now gives d(y)<=15
for every y in Y union Z, and hence residual degree at most10 after removing
the twenty prescribed cones. Write r=|F|-20, so r>=48.

## The only extra local premise used after internal removal

On a central anchor {x,a,b,c}, if its singleton class at y is at least8,
B4 makes the complementary link part K_y intersecting. It contains all five
triples {x} union E for E in the C5 link of y within its P10 component. Any
additional triple avoiding x would have to meet every edge of that C5. A
vertex cover of C5 needs at least three vertices. Since a triple has exactly
three points, all its points would belong to the same component, producing
an excluded internal four-member after adjoining y. Therefore |K_y|=5.

Consequently, if an actual marked residual has a trace of size at least two
through y on this central anchor, it adds a sixth member to K_y. The singleton
class at y must then have size at most7. This argument is universal after
internal removal and uses neither H27 nor a closed-neighbourhood minimum.

## Six exact certificates

Consider the six marked residual types below. The symbol12 denotes an exterior
point, not a member of either six-point component.

| Case | Marker | Scale L | Weighted RHS H | Marker coefficient q(M) | Bound on r |
|---|---|---:|---:|---:|---:|
| E00 | {0,1,2,6} | 2 | 81 | 3 | 40 |
| E01 | {0,1,2,12} | 2 | 91 | 3 | 45 |
| E02 | {0,1,3,6} | 2 | 80 | 3 | 79/2 |
| E03 | {0,1,3,12} | 3 | 141 | 4 | 140/3 |
| E04 | {0,1,6,7} | 10 | 430 | 10 | 43 |
| E05 | {0,1,6,12} | 1 | 48 | 2 | 47 |

The literal integer row weights are in `stage2-certificates.json`. The checker
`check_stage2_certificates.py` does not import scipy, a solver, any source
signature catalogue, or the original model builder. It independently validates
every row as one of the following types:

* Global point/pair/triple incidence capacities20/6/2, subtracting the actual
  contributions of the twenty fixed cones.
* Exact singleton/pair/triple capacities10/3/1 on an actual cone or marker,
  again subtracting fixed contributions.
* Residual degree at most10 at a link point after internal removal.
* Exact singleton at most7, with the literal marker intersection verified to
  satisfy the preceding K_y argument.
* One elementary mixed-sign row in E04, justified next.

For E04 use central anchor {x,6,7,8}. Let a,c,e,s count exact traces67,78,678,7.
The marker has exact trace67, so a>=1. The degree cap at7 gives
a+c+e+s<=10. Therefore

    c+s-9(a+e) <= 10-10(a+e) <=0.

This is the only mixed-sign local inequality. All former convex-combination
variables and imported local-row catalogue restrictions have disappeared from
the final certificates. In particular, none of the mu41 or pair-degree-sum19
conditions used during discovery are needed in these checked row lists.

For each residual Q, let S be its exact trace on the twelve link points,
together with the one exterior point12 if that point occurs in the marker.
Distinct residuals with the same proper trace are counted with multiplicity.
Internal traces and traces forming a literal sunflower with M and a fixed cone
are impossible. For every other trace the checker verifies q(S)>=L, where q
is the weighted sum of the row coefficients. There are794 traces without a
marked exterior point and1093 with one. As M occurs, it contributes its exact
extra coefficient q(M)-L, giving

    L*r + q(M)-L <= sum_Q q(S(Q)) <= H.

Every bound in the table is strictly below48. Unknown exterior points affect
none of the marked intersections or row counts. Thus all six marked types
are excluded in the putative family.

The checker also enumerates all720 permutations of a component to obtain the
sixty automorphisms of P10. Canonical signatures in each component, together
with component interchange, verify the six exhaustive orbit types among all
685 non-internal four-sets with three or four link points, using one canonical
exterior point when needed. Their counts are120,20,120,20,225,180 respectively.
Arbitrarily many other exterior labels do not add an orbit type. No completion
is assumed symmetric. We conclude that every residual has at most two link
points.

## Ordinary final double count

If a residual M={y,z,a,b} has y in Y,z in Z and exterior a,b, then every
residual Q contains {y,z} or meets {a,b}. To see this, suppose Q avoids a,b.
If Q misses y,z, one component contains at most one point of Q; choose a P10
block there avoiding both its marked point and Q's possible point. Its cone
is disjoint from both M and Q, a forbidden empty-core sunflower. If Q meets
exactly y, choose a P10 block through y avoiding Q's possible other point in
Y. Its cone, M and Q form a sunflower with core{y}. The case z is symmetric.
These choices exist because P10 has point degree5 and pair codegree2.

The three covering categories have capacities6,20,20. M belongs to all three,
so its two redundant counts can be subtracted. Thus r<=6+20+20-2=44, giving
|F|<=64, a contradiction. Therefore no residual has a mixed link pair.

Every residual consequently meets at most eight fixed cones: a same-component
pair meets5+5-2=8; a singleton or empty trace meets fewer. It is disjoint from
at least twelve cones. For each fixed cone C, the members disjoint from C are
intersecting, since two disjoint such members would form an empty-core
sunflower with C. H27 bounds that class by27. Double counting disjoint pairs
between the twenty cones and all residuals gives

    12*r <=20*27=540, hence r<=45 and |F|<=65.

This contradiction proves the stated branch theorem.

## Evidence and remaining scope

`stage2-check.json` records exact cover histograms, row types, rational bounds,
orbit coverage and hashes. It is certificate-diagnostic; the written argument
provides the arbitrary-ground-set interpretation. A complete Lean proof of the
structural premises, finite covers and counting bridge has not been claimed.
The separate Local51 arithmetic implication is axiom-audited in Lean.

The new conclusion removes degree20 from a hypothetical68-member counterexample.
The degree19, degree18, degree17 and lower-degree/bootstrap cases remain to be
settled at the new threshold. Thus the strongest located global numerical
upper-bound claim remains68; no final-review/publication gate is opened here.
