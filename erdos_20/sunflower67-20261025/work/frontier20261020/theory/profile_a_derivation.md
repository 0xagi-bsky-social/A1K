# Profile A: extremal-star nonextension derivation

Status: ordinary mathematical derivation; not yet an assembled Lean theorem. Uses the ordinary hypothesis `IntersectingRankFourUpper 27`. Exact finite diagnostics below are not Lean evidence. The pinned definition is `Erdos20V13Boundary.ProfileARealizable`.

## Frozen model

Let F be a 3-sunflower-free family of 81 distinct four-element sets with support partition `{x} ⊔ A ⊔ B ⊔ O`, where |A|=|B|=6, |O|=4. The 20 members containing x are x adjoined to two disjoint copies D_A,D_B of the unique intersecting ten-triple design. Every non-x point has degree 19. Let H be the 61 members omitting x. Every point in A∪B has H-degree 14; every point in O has H-degree 19. The existing A1K classification and normal-form theorems supply this model from Profile A.

Write H_i={R∈H: |R∩O|=i}, n_i=|H_i|. All intersection and sunflower conventions are literal set intersections; empty-core sunflowers count.

## A. Disjointness forces few outsiders

For every R∈H,

  2 |{S∈H:S∩R≠∅}| ≤ Σ_{v∈R} d_H(v)+38.

This follows from the singleton trace bound 40 and the exact point-incidence defect. Since d_H≤19, every R has at least 61−57=4 disjoint members S of H.

For disjoint R,S∈H, R∪S must meet every triple in D_A∪D_B: an avoided triple T would make R,S,{x}∪T an empty-core sunflower. The high link has transversal number six. Therefore the eight-point union R∪S has at least six points in A∪B, and at most two points in O.

Consequently H_i is empty for i≥3; H_2 is intersecting and meets every member of H_1. The incidence identities are

  n_0+n_1+n_2=61,   n_1+2n_2=76,   n_2−n_0=15.

Apply I(27) to H_2 to get n_2≤27 and n_0≤12. For any R∈H_2 the degree sum is 2·14+2·19=66, hence its meeting neighborhood has at most 52 members. It has at least nine disjoint members; all of them belong to H_0. Thus n_0≥9 and n_2≥24.

## B. A split neighbor pair allows only four disjoint completions

Suppose R∈H_2 has P=R∩(A∪B)={a,b}, a∈A,b∈B. For any S∈H disjoint from R, P∪S is a six-point transversal of D_A∪D_B. Every minimum transversal is one triple of D_A together with one triple of D_B. Hence S=e_A∪e_B where e_A is an edge in the five-cycle link of a in D_A, and e_B is an edge in the five-cycle link of b in D_B.

Any two such completions S=e_A∪e_B and S'=f_A∪f_B must have both e_A∩f_A≠∅ and e_B∩f_B≠∅. To prove this, assume e_B∩f_B=∅:

* If e_A∩f_A=∅, then R,S,S' are pairwise disjoint.
* If e_A=f_A, the high member {x,a}∪e_A forms a sunflower with S,S', core e_A.
* If e_A∩f_A={q}, write the other endpoints r,s. There is a triple T∈D_A containing q and avoiding r,s: q has degree five and each pair has codegree two, so at most four of its five triples contain r or s. Then {x}∪T,S,S' form a sunflower with core {q}.

The symmetric assertion follows for A. A pairwise-intersecting subfamily of edges of C5 has at most two edges. Thus there are at most 2·2=4 possible disjoint completions S. This contradicts the required nine.

It follows that every H_2 member has its two non-O points in the same design support.

## C. All H_2 members choose the same design support

If an H_2 member has its neighbor pair in A, each of its disjoint H_0 completions has shape (one A point)+(a D_B triple). This follows again from the minimum-transversal characterization. Hence there are at least nine H_0 members of type (1,3) in A×B. A member whose neighbor pair is in B would require at least nine H_0 members of the disjoint type (3,1). Since n_0≤12, both types of H_2 cannot occur.

Relabel A,B if necessary. All at least 24 H_2 members have their neighbor pair in A.

## D. Extension-pair weights give the contradiction

Let W⊆H_0 consist of members {a}∪T, a∈A,T∈D_B. Each fixed T occurs at most once: two distinct extensions by a,a' would form a sunflower with {x}∪T. Thus |W|≤10.

For each pair P⊆A define E(P) as the two points q with P∪{q}∈D_A. Every pair has exactly two extensions. In the canonical ten-triple design, P↦E(P) is a bijection on the 15 two-element subsets of A. This is a finite normal-form fact, independently checked by exact enumeration; it remains to be included in the Lean root closure.

Let K be the set of pairs P used by H_2. Every such P has at least nine disjoint H_0 completions. These are exactly the members {a}∪T of W with a∈E(P). If E(P) and E(Q) were disjoint, their two sets of at least nine W members would be disjoint, contradicting |W|≤10. Therefore the distinct extension pairs form an intersecting family of two-element subsets of a six-point set. Such a family has at most five pairs: it is a star, of size at most five, or it is contained in a triangle, of size at most three. By injectivity, |K|≤5.

For each fixed P∈K, the outside pairs Q⊆O for which P∪Q∈H form a 3-sunflower-free graph on four points. Every vertex has degree at most two, because three incident edges are a 3-sunflower. Double counting gives at most four edges. Hence

  |H_2| ≤ 4|K| ≤20,

contradicting |H_2|≥24.

## Precise proposed theorem

Under the existing rank-three extremal classification (already proved in the pinned project) and I(27), no Profile A family exists. Equivalently, target

  `IntersectingRankFourUpper 27 → ¬ ProfileARealizable`.

This proof does not discharge I(27), does not exclude Profile B, and by itself does not establish RankFourUpper 80. The route has no external UNSAT premise. Its remaining burden is actual-family bookkeeping and the small normal-form facts (five-cycle links, extension-pair permutation) in Lean.

## Diagnostics and formal progress

* `completion_bound.py`: exact finite set construction plus Z3 optimization; same-block pair gives maximum ten completions; split pair gives maximum four. These outputs motivated the structural argument but are not premises of the proof above.
* `../compute/verify_a_split.py`: independent exact verification over all 36 split pairs, C5 coordinate compatibility, and extension-pair injectivity, reported by the compute branch.
* `../formal/MeetingDefect.lean`: degree-sensitive meeting inequality and nine-disjoint corollary, authored by the formal branch.
* `../formal/MinimumTransversals.lean`: six-point transversal structure, authored by the formal branch.

## Closed proof update (2026-10-20)

The ordinary derivation is now assembled in Lean as
`FrontierProfileAClosed.no_profile_a_of_intersecting_twenty_seven`, with exact type
`IntersectingRankFourUpper 27 → ¬ ProfileARealizable`. The actual-family residual
bridge, synchronized two-design geometry, concentration, disjoint-completion mass,
and outside fibers are in its proved dependency closure. The thirteen theory roots
pass the fail-closed axiom allow-list audit, admitting only `propext`,
`Classical.choice`, and `Quot.sound`. Assurance: `axiom-audited`; cached dependencies
and same evaluator, not independent reproduction or clean replay.

The final proof improves Step D: it does not use canonical coordinates or an
extension-pair permutation certificate. Any two-point extension set carrying at
least nine of ten total units has a point of weight at least five. Every other
heavy extension set must contain that point, since otherwise its nine units plus
the omitted point's at least five units exceed ten. All used design-side pair keys
therefore extend through one common design point. The exact degree-five property
of the ten-triple design directly gives at most five keys. This removes the finite
normal-form premise from the closure.

Profile A alone still does not establish the eighty bound; Profile B and the local
I(27) discharge remain logically separate. No global priority claim is made here.
