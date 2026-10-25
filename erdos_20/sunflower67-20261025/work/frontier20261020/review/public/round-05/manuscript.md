# Excluding both eighty-one-member boundary profiles in rank-four sunflower-free families

**A1K mathematical research · 20 October 2026**

Research manuscript. This is a fixed-rank result. The general Erdős–Rado sunflower conjecture remains open in this work.

## Abstract

Let G(N) assert that every finite family of distinct four-element sets containing no three-petal sunflower has at most N members; let I(N) be its intersecting analogue. Empty sunflower cores are permitted. We prove the implication I(27) ⇒ G(80) by excluding both actual eighty-one-member boundary profiles left open in the pinned A1K version-thirteen development. The single-high-point profile is excluded by disjoint-completion geometry and concentration of extension-pair weights. The two-high-point profile is excluded by a short incidence argument. The latter yields an unconditional structural theorem: a four-uniform three-sunflower-free family containing two distinct degree-twenty points which never occur together has at most eighty members, with no restriction on its ground-set size. These are proofs about actual set families, rather than numerical profiles or finite search diagnostics.

The final implication, both profile exclusions and the two-star theorem have passed Lean 4.26.0 elaboration and fail-closed axiom audits allowing only `propext`, `Classical.choice` and `Quot.sound`. I(27) remains an explicit hypothesis of the local Lean implication. Applying the external computer-assisted I(27) theorem of Axante, Budala, Chitic, Dumitru and Nacu gives the ordinary mathematical corollary 54 ≤ f(4,3) ≤ 80. This use of an external theorem is not an unconditional Lean proof of G(80). The inspected preprint states the upper bound 83; the earlier A1K implication already gave 81 from the same external I(27). The present improvement is therefore three below that preprint's bound and one below the earlier A1K corollary. Bounded primary-source searches support this comparison, not an exhaustive global-priority claim.

## 1. Definitions, scope and inherited inputs

A sunflower consists of three distinct members S,T,U with S∩T=S∩U=T∩U; the common intersection can be empty. Families and their members are finite sets, so repetitions are excluded. Write d_F(v) for the number of members containing v, supp(F) for their union, and L_x={R∖{x}: R∈F, x∈R} for the link of a point x. A high point has degree twenty. A family is intersecting when every two distinct members have nonempty intersection. For four-element members this agrees with the formal predicate that also permits the two members to be equal. We define f(4,3) as the maximum cardinality of a four-uniform three-sunflower-free family, rather than the forcing threshold; the smallest size that forces a sunflower is f(4,3)+1.

The pinned A1K development supplies the following statements, which are inherited rather than contributions of this manuscript:

1. Point degrees in a four-uniform three-sunflower-free family are at most twenty. A twenty-member triple link has two intersecting ten-triple components on disjoint six-point supports. Each component is a simple 2-(6,3,2) design: each point has degree five and each pair has codegree two. Its point links are five-cycles. The complete twenty-link has transversal number six.
2. There are at most two high points in any such family.
3. I(27) implies G(81). Under I(27), every eighty-one-member family has seventeen supported points and one of two degree profiles. Profile A has one degree-twenty point and sixteen degree-nineteen points. Profile B has two degree-twenty points, fourteen degree-nineteen points and one degree-eighteen point. Every member contains at most one high point.
4. Consequently I(27), exclusion of A and exclusion of B together imply G(80).

From the inherited component properties we additionally prove a synchronized minimum-transversal lemma: every six-point transversal of the complete twenty-link is one design triple from each component. Its root is `FrontierMinimumTransversals.two_designs_transversal_six`. This assembly is part of the present development.

These inherited inputs are implemented in the Lean sources at A1K commit `0e9aee578a7bb3dbc665630c759297514f88a81d`. The public [version-thirteen report](https://a1k.ai/agentic-math/rank-four-sunflower-free-families) and [repository](https://github.com/0xagi-bsky-social/A1K) explicitly leave all three inputs to the final eighty implication open. The present work discharges A and B. It does not independently discharge I(27).

The previous local release's support reductions from 85 to 56 and 53 points also remain valid, but are not premises of the new profile exclusions. No Fin 53 enumeration is used here.

## 2. Main statements and assurance boundary

**Theorem 1 (two independent twenty-stars).** Let F be a finite four-uniform three-sunflower-free family. If distinct x,y have d_F(x)=d_F(y)=20 and no member contains both, then |F|≤80. The ambient support is unrestricted.

**Theorem 2 (single-high boundary exclusion).** Assume I(27). No family realizes Profile A.

**Theorem 3 (terminal implication).** I(27) implies G(80).

**Corollary 4 (ordinary bound using an external theorem).** Applying the computer-assisted I(27) upper bound in Proposition 6.7 (with the exact intersecting maximum in Proposition 6.8) of [Axante et al., arXiv:2609.06175v1](https://arxiv.org/html/2609.06175v1#S6.SS3) to Theorem 3 yields f(4,3)≤80. Together with the known construction of size 54, this gives 54≤f(4,3)≤80.

The distinction between Theorem 3 and Corollary 4 is part of the result. In Lean, I(27) is an ordinary universally quantified argument, never a project axiom. The external enumeration establishing it has not been imported into the proof kernel. Corollary 4 is an ordinary mathematical deduction using that external theorem, with its computational provenance retained.

## 3. The two-star argument

Let x,y be as in Theorem 1. Put U=supp(L_x), V=supp(L_y), C=U∩V, q=|C|, and let H be the members containing neither center. The two stars are disjoint families of twenty members each, so |F|=40+m, where m=|H|. Both U and V have size twelve. Neither center lies in the other's link support. Since the inherited global high-point bound is two, every other point has degree at most nineteen.

### 3.1 Every residual member meets each link support at least three times

First observe that if R,S avoid x and are disjoint, then R∪S meets every triple of L_x. Otherwise R,S and an x-star member form an empty-core sunflower. Since L_x has transversal number six, the eight-point union R∪S has at most two points outside U.

Now suppose R∈H has at most two points in U, so at least two points outside U. For any Q∈L_y, the member {y}∪Q contains a point y outside U. It cannot be disjoint from R, by the preceding outside-point bound. Since y∉R, Q must meet R. Thus R would be a four-point transversal of L_y, contradicting its transversal number six. We have proved |R∩U|≥3; symmetrically |R∩V|≥3. As |R|=4, it follows that |R∩C|≥2.

This is a universal, independently reusable structural lemma. Its proof uses neither a finite support restriction nor a coordinate enumeration.

### 3.2 Incidence deficit on the overlap

Each point of U belongs to five x-star members, so its degree in H is at most 14. A point of C belongs also to five y-star members; the two star families are disjoint, so its H-degree is at most 9. Double counting gives

$$
2m\le9q,\qquad
3m\le14(12-q)+9q=168-5q\text{.}
$$

Multiply the second inequality by 9 and the first by 5 and add. The q terms cancel:

$$
37m\le1512<37\cdot41\text{.}
$$

Therefore m≤40 and |F|≤80. In particular, Profile B, which would have m=41, is impossible. The proof does not use the unique degree-eighteen point or the seventeen-point support restriction of B.

The formal development proves the more general incidence lemma

$$
37|H|\le126|U|
$$

for any four-uniform H whose members meet U,V at least three times, with H-degrees at most 14 on U and at most 9 on U∩V. This lemma has no sunflower hypothesis; the preceding structural argument supplies its hypotheses in the application.

## 4. The single-star boundary argument

Assume I(27) and suppose F realizes A. Let x be its unique high point. The two design supports of L_x are A,B, each of size six, and let O be the four other supported points. Delete the twenty x-star members to obtain H of size 61. Points of A∪B have H-degree 14 and points of O have H-degree 19.

For R∈H, let M_H(R) be its closed meeting neighborhood. A degree-sensitive trace inequality gives

$$
2|M_H(R)|+2\le\sum_{v\in R}d_H(v)+40\text{.}
$$

For completeness, the singleton exact-trace classes contribute at most 10 each. In the point-incidence sum, every nonsingleton trace contributes at least twice, while R itself contributes four instead of two. Hence the sum is at least 2|M_H(R)| minus the singleton total plus 2, proving the inequality. Its use here is on the actual family H.

### 4.1 Outsider census and nine disjoint completions

Every R has a disjoint member because the displayed bound and d_H≤19 give |M_H(R)|≤57<61. The union of two disjoint H-members is a transversal of L_x; it therefore has at most two points in O. In particular every H-member has at most two outsiders.

Let H_i={R∈H: |R∩O|=i}, and n_i=|H_i|. Counting members and outsider incidences gives

$$
n_0+n_1+n_2=61,\quad n_1+2n_2=76,\quad n_2=n_0+15\text{.}
$$

H_2 is intersecting: two disjoint members would have four outsiders in their union. I(27) gives n_2≤27 and hence n_0≤12. For R∈H_2, its degree sum is 66, so the meeting bound improves to |M_H(R)|≤52. Each such R consequently has at least nine disjoint completions, all in H_0. Thus

$$
9\le n_0\le12,\qquad24\le n_2\le27\text{.}
$$

### 4.2 A split pair has at most four completions

Suppose R∈H_2 has one non-O point a∈A and one b∈B. For any disjoint S∈H_0, the six-point set {a,b}∪S is a minimum transversal of L_x, hence a triple from each design. Thus S=e_A∪e_B, with e_A an edge in the five-cycle point link at a and e_B an edge in the point link at b.

The coordinate edges from any two completions must intersect in both coordinates. To see this, suppose their B-edges are disjoint. If their A-edges are also disjoint, the two completions and R form an empty-core sunflower. If their A-edges coincide, the corresponding x-star member gives a sunflower with that edge as core. If the A-edges meet only at q, let their other endpoints be r,s. Of the five design triples through q, at most two contain r and at most two contain s. A triple through q avoiding r,s therefore exists, and its x-star member forms a sunflower with core {q}. Each possibility contradicts sunflower-freeness. The symmetric argument applies to the other coordinate.

An intersecting subfamily of the edges of a five-cycle has at most two edges. Therefore the completions number at most 2×2=4, contradicting the lower bound nine. Every H_2 member has its two non-O points in the same design support.

### 4.3 One orientation and a common extension point

If the pair is in A, each disjoint completion has one point in A and a design triple in B, by the same minimum-transversal characterization. This requires at least nine H_0 members of type (1,3). A pair in B would require at least nine members of the disjoint type (3,1). Since n_0≤12, both orientations cannot occur. Exchange A,B if necessary so all H_2 pairs lie in A.

Let W be the H_0 members consisting of a point a∈A and a design triple T⊆B. Each T has at most one such extension: two different extensions together with {x}∪T form a sunflower with core T. Thus |W|≤10. Assign to a∈A the weight equal to the number of members of W using a.

Let K be the pairs P⊆A used by H_2. The design has precisely two extension points E(P)={a∉P: P∪{a} is a design triple}. Every one of the at least nine disjoint completions of a row with key P uses a point in E(P). Consequently E(P) carries weight at least nine.

The following weighted-pair observation is reusable: for a nonempty collection of two-element sets, with nonnegative integer point weights totaling at most ten, if every set carries at least nine units then all the sets contain a common point. In the present application, choose any used P; such a pair exists since n_2≥24. One of its two extension points, say a, has weight at least five. Every other E(Q) must contain a: otherwise its weight at least nine and the omitted point's weight at least five would exceed the total weight at most ten. Hence all used keys Q extend through one common design point a. The map Q↦Q∪{a} is injective into the five design triples through a, so |K|≤5. No canonical extension-pair permutation check is required for this step.

For a fixed key P, the outsider pairs Q⊆O with P∪Q∈H form a sunflower-free graph on four points. Its vertex degrees are at most two, because three incident edges would lift to a sunflower. It therefore has at most four edges. Finally n_2≤4|K|≤20, contradicting n_2≥24. Profile A is excluded.

## 5. Formal interfaces and reproducibility

The principal new roots are:

| Mathematical result | Lean declaration |
|---|---|
| Three-point trace in either link support | `FrontierTwoStarResidual.residual_meets_link_support_ge_three` |
| General overlap incidence inequality | `FrontierTwoHighIncidence.two_large_traces_incidence_bound` |
| Two independent twenty-stars imply at most 80 | `FrontierTwoHighEighty.independent_twenty_stars_card_le_eighty` |
| Literal Profile B exclusion | `FrontierTwoHighEighty.profile_b_not_realizable` |
| I(27) excludes literal Profile A | `FrontierProfileAClosed.no_profile_a_of_intersecting_twenty_seven` |
| I(27) implies G(80) | `FrontierFinalEighty.rank_four_upper_eighty_of_intersecting_twenty_seven` |
| Fully expanded terminal proposition | `FrontierFinalEighty.literal_intersecting_twenty_seven_implies_eighty` |

The inherited global-bound interface quantifies over `α : Type`; the final expanded proposition preserves that exact interface. The structural two-star and incidence lemmas are universe-polymorphic (`Type*`). All families are finite, with no fixed support size in the public mathematical bound. Decidable equality is the standard interface for finite sets; classical reasoning is explicitly within the allowed logical foundation.

The toolchain is Lean 4.26.0, commit `d8204c9fd894f91bbb2cdfec5912ec8196fd8562`, with mathlib commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Audits fail if a root is missing, is not a theorem, has a non-propositional type or depends transitively on an axiom outside the three-name allow-list. The roots do not depend on `sorryAx`, `native_decide`, project axioms or trusted external evaluation. The final claim's assurance grade is **axiom-audited**. Compilation uses the same evaluator and pinned dependencies; this is not independent human certification or a complete clean-toolchain replay.

Source files, exact commands, source hashes, output logs and failed attempts are retained outside the three-format manuscript directory. The completed source-closure rebuild covered 161 modules: 63 were compiled freshly and 98 inherited modules were reused only after their prior successful rebuild receipt matched the current source hash. All final roots were audited again in that closure. The final receipt and manifest govern the exact coverage; the manuscript does not infer source verification from the existence of an object file.

## 6. Exploratory computations and non-results

The new local structural arguments retain I(27) as a hypothesis where stated. Corollary 4 additionally uses the external enumerative I(27) theorem. The exploratory computations below are not premises of the local proofs; they document the search and unsuccessful routes.

An exact diagnostic explored whether two independent twenty-stars admit at most five residual members, suggesting the much stronger total bound 45. Separate Python and C++ implementations agreed across 156,960 canonical relative geometries and 20,475 candidate four-sets on 28 normalized positions. All permitted residual candidates were inside the actual union of the two link supports. However, the normalization and complete finite checking pipeline have not been connected to a Lean theorem. **The universal upper bound 45 is not established here.** An explicit 45-member family passes external exact checks; attempts to verify its bitmask witness in Lean reached the imposed 100-second resource limit. Those failed attempts are not counted as proof receipts.

A Profile A SAT model was constructed but its bounded solver run returned UNKNOWN. No SAT witness or UNSAT certificate was obtained. The final proof excludes A without that solver. Optional variable-degree and equality-case refinements are exploratory notes, not additional accepted claims of this manuscript.

## 7. Literature comparison, contribution and remaining work

The external I(27) input is clearly delimited. Axante et al.'s preprint establishes the intersecting upper bound in Proposition 6.7, the exact maximum in Proposition 6.8, and 54≤f(4,3)≤83 in Theorem 6.9. It separately describes Lean coverage of other arguments and witnesses; the intersecting upper enumeration is not supplied here as a kernel-checked Lean proof. The external result is used as a mathematical theorem, not silently reclassified as formal evidence.

The new contribution is the actual-family exclusion of both remaining eighty-one-member profiles, with a reusable two-star trace lemma, a general overlap incidence inequality and a common-extension-point concentration argument. These close the A1K conditional eighty endpoint and, when combined with the explicit external theorem, improve the compared numerical bound. The previous 53-point support reduction did not itself do this.

Primary-source searches on 20 October 2026 covered the exact f(4,3) notation, rank-four and four-uniform sunflower-free upper bounds, eighty/eighty-one formulations, degree-twenty structure, the named preprint and the public A1K repository. No additional primary source establishing an equal or stronger unrestricted numerical bound was verified in that search. This statement records search coverage only. It does not establish exhaustive absence, peer-reviewed priority, global consensus or independence of the agents. A separate proof-tracking page returned by the search discussed conditional all-rank mechanisms; no relevant unconditional rank-four bound was identified from it.

The main remaining formal obligation is a local kernel-checked proof of I(27), or a sound imported enumeration certificate. The stronger two-star cap 45 and its normalization remain a separate research target. None of these results proves a fixed-base exponential bound for every rank. The all-rank sunflower conjecture, exact value of f(4,3), global novelty and independent expert certification are not claimed.

## References and evidence

1. Edward Axante, Cristian Budala, David Chitic, Bogdan Dumitru and Mihai Nacu. *Sunflower-Free Uniform Families: Recursive Constructions and Explicit Bounds*. arXiv:2609.06175v1, 5 September 2026. [Record](https://arxiv.org/abs/2609.06175); [Section 6.3](https://arxiv.org/html/2609.06175v1#S6.SS3); [formalization scope](https://arxiv.org/html/2609.06175v1#S8).
2. A1K. *Transversal Six, Finite Obstructions and Boundary Profiles in Rank-Four Sunflower-Free Families*, version 13, 22 September 2026. [Report](https://a1k.ai/agentic-math/rank-four-sunflower-free-families); [Lean repository](https://github.com/0xagi-bsky-social/A1K). Inherited source pin given in Section 1.
3. This development, `work/frontier20261020`: `formal/`, `theory/`, `compute/`, their proof receipts and `closure-rebuild/`. Exploratory records and resource failures remain separate from accepted roots.

The accompanying immutable review bundle records completed autonomous specialist rounds and final acceptance decisions. The review process uses actual separate agent contexts under one orchestration environment. Such review is not independent human certification.
