# A 53-point finite reduction for intersecting rank-four sunflower-free families

## Abstract

We prove that every intersecting family of 28 distinct four-element sets containing no three-sunflower has at most 53 supported points, over an ambient type in any universe. The entire support argument is assembled in Lean, together with the equivalence between the intersecting upper bound I(27) and absence of the corresponding obstruction on Fin 53. Three-star and four-star corrections to an incidence second moment combine with degree bounds and small kernel-checked numerical inequalities; the intermediate capacities 72 and 56 are also formalized. These results strengthen the pinned A1K finite reduction from capacity 85. They do not exclude the finite obstruction or improve a sunflower extremal value. The literature already reports I(27) by computer-assisted enumeration. We present exact proof interfaces, local compilation and axiom-audit coverage, reproducibility limits, and the remaining certificate obligation without claiming global originality.

## Scope, conventions, and prior work

A family is finite and has distinct members. Rank r means every member has exactly r points. A three-sunflower consists of three distinct members with equal pairwise intersections; the common core may be empty. Intersecting here means every two members meet, including a member paired with itself; this is the literal formal interface and has no effect for positive rank. The support is the union of the members. The degree d(x) counts members containing x, and a codegree counts members containing a specified subset. The ambient type need not be finite and may lie in any universe. Write I(27) for the assertion that every intersecting rank-four three-sunflower-free family has at most 27 members; f(r,3) is the maximum size of an unrestricted rank-r three-sunflower-free family.

The starting library is A1K commit `0e9aee578a7bb3dbc665630c759297514f88a81d`, with Lean 4.26.0 and mathlib `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` [1]. Its version 13 finite reduction uses Fin 85. Its unrestricted bound 80 remains conditional on three inputs: the intersecting upper bound I(27), and nonrealizability of each of two explicit 81-member boundary profiles. None of those three inputs is discharged here [1,2].

The preprint of Axante, Budala, Chitic, Dumitru and Nacu already reports the intersecting maximum 27 by computer-assisted canonical enumeration, together with 54 <= f(4,3) <= 83 [3]. Therefore I(27) is an unresolved input of the local protected Lean development, not a newly identified open problem in the entire literature. Our hypothetical 28-member class is empty if their computer-assisted result is imported. The support reduction is useful as a smaller independent target for a kernel-checked exclusion; it does not improve their extremal value. Their paper separates its computational exclusions from its Lean-formalized scope.

The OpenAI mathematics corpus was inspected in the preceding audit at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The current head `1581d4cbdd69a0faf34b2089614fe2a814316a6a` changes only a GitHub workflow. Its spread-counting inequalities and finite-certificate proof architecture informed the research choices, but no OpenAI theorem is a premise of the results below. We did not transplant its much larger expectation-threshold constants into the sharp finite problem [4].

## Methods and assurance

Exploratory research examined finite support and related local configurations. This report retains the completed support reductions and their generic counting lemmas. The four-star refinement was developed after the three-star bound; it was an exploratory extension, not a preregistered outcome. Claims are separated into mathematical arguments, executable diagnostics, and successful Lean declarations. The allowed foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`; no project axiom, `sorry`, or `native_decide` is admitted into a released protected root.

A matching Lean 4.26.0 runtime was located locally. All nine dependency revisions matched the pinned manifest; all 155 retained project source files matched the pinned source bytes. After an initial successful new-module replay, the entire root-reachable project source closure was rebuilt: 100 inherited A1K modules first, then all 14 new modules against those fresh objects, in initially empty output directories. All source hashes remained stable, all modules exited successfully, and all 66 named roots passed the final axiom audit. The composite replay receipt binds the new-module input base to the freshly rebuilt A1K modules; its child receipt retains conservative generic cache wording. This replay uses no retained A1K compiled objects. Lean, mathlib and third-party package objects remain cached. It supports source-closure elaboration and axiom auditing, not a clean rebuild of the entire dependency tree or an independently controlled reproduction.

The small Python computations use exact integers or rational arithmetic where stated. They remain diagnostic unless an explicit semantic bridge and kernel-checked evaluator are in the protected closure. Failure to finish a search establishes neither satisfiability nor unsatisfiability. A bounded literature search does not certify global originality.

## A general support inequality and the checked Fin 72 reduction

**Theorem 1.** Let F be an intersecting r-uniform finite family of m members. Let n be its support size, and suppose every point degree is at most D. Then

$$D n + m(m+r-1) \leq (D+1)rm\text{.}$$

For r=0 the only possible intersecting family under our convention is empty; the Lean statement uses natural subtraction r-1 and covers this endpoint explicitly. For positive r the displayed expression has its ordinary integer meaning.

**Proof.** For each member S, the incidence sum of its r points is at least m+r-1: every other member contributes at least one, and S contributes r. Summing over S gives

$$\sum_x d(x)^2 \geq m(m+r-1)\text{.}$$

For every supported point, 1 <= d(x) <= D, hence

$$d(x)^2+D\leq(D+1)d(x)\text{.}$$

Sum this inequality over the support and use the incidence identity sum_x d(x)=rm. This gives the asserted bound. The proof uses no sunflower assumption.

**Corollary 1.** If F is an intersecting 28-member family of four-element sets containing no three-sunflower, its support has size at most 72. The inherited A1K degree bound is D=19. Thus 19n+868 <=2240, giving n<=72.

The declarations `FrontierSupport.intersecting_degree_support_inequality` and `FrontierSupport.intersecting_twenty_eight_support_le_seventy_two` elaborated successfully. The terminal declaration `FrontierSupport.intersecting_upper_twenty_seven_iff_no_finite72_obstruction` proves

$$I(27)\ \Longleftrightarrow\ \text{there is no intersecting 28-member, rank-four, three-sunflower-free family on Fin 72}\text{.}$$

The proof selects exactly 28 members from any counterexample and reuses A1K's injective support relabeling. It does not execute or settle the finite exclusion. A separate checked Boolean-incidence lemma characterizes equality of the three pairwise intersections by absence of a point contained in exactly two of the three sets; distinctness and row cardinalities remain necessary in any complete SAT encoding.

## A three-star second-moment correction

**Theorem 2.** Let F be an intersecting r-uniform family with m members. For any three distinct points, let x,y,z be their three pair-codegrees and t their triple-codegree. Then, with all expressions interpreted over the integers,

$$\sum_v d(v)^2 \geq m(m+r-1)+x(x-1)+y(y-1)+z(z-1)-t(t-1)\text{.}$$

This statement does not assume sunflower-freeness. Its use here is to retain overlap information that a plain incidence bound discards. It is an elementary double-counting consequence; broad literature novelty has not been established. The universal declaration `FrontierSupport56.three_star_second_moment` has compiled with exit code zero and only the three foundational axioms listed above. It uses integer casts and subtraction exactly as displayed, with pairwise distinct chosen points and the stated uniformity and intersection hypotheses.

**Proof.** For any nonempty intersection I of two distinct members, let j be the number of the three chosen points lying in I. Then

$$|I|-1\geq \binom{j}{2}-\binom{j}{3}\text{.}$$

For j=0,1 this follows from nonemptiness; for j=2,3 the right side is j-1 and |I|>=j. Summing over unordered distinct member pairs yields the correction, because each selected point-pair contributes binom(codegree,2) and the selected triple contributes binom(t,2). Finally, twice the sum of member-pair intersection sizes is sum_v d(v)(d(v)-1), and sum_v d(v)=rm. This gives the stated formula. The diagonal is thus accounted for exactly, rather than discarded.

## Top-three-star correction and the Fin 56 target

The following proof strengthens the actual support bound to 56. Both the finite leaf and the combinatorial bridges are assembled in the checked universal declaration `FrontierSupportFinish.intersecting_twenty_eight_support_le_fifty_six`.

**Theorem 3 (support 56).** If F is an intersecting 28-member family of distinct four-element
sets, containing no three-member sunflower (empty core included), then its actual
support has size at most 56. This concerns the actual support, not a quotient or
point-identification compression.

Write n for support size and d_v for point degrees. The shipped A1K theorem
`Erdos20ExtremalTransversals.intersecting_rank_four_card_ge_twenty_one_degree_le_nineteen`
gives d_v<=19. The pair-codegree bound is <=6. A triple-codegree is <=2: three
distinct four-sets containing the same triple would have distinct fourth points
and form a sunflower with that triple as core. These are the only sunflower
inputs used below.

Let

    P = sum_v binom(d_v,2),     W=P-binom(28,2)=P-378.

Counting incidences gives sum_v d_v=112. Counting unordered pairs of distinct members
through their shared points gives P=sum_{A<B}|A intersect B|. Since F is
intersecting, W=sum_{A<B}(|A intersect B|-1)>=0.

Assume n>=57. Choose three points of highest degrees a>=b>=c. There are at least
three support points. Every remaining point has degree in [1,c]. Put s=112-n,
so s<=55. From d(d-1)<=c(d-1) on those remaining points,

    2P <= a(a-1)+b(b-1)+c(c-1)+c*(s-a-b-c+3)
       <= U := 55c+(a-c)(a-1)+(b-c)(b-1).                  (1)

The expression s-a-b-c+3 is exactly the sum of (d_v-1) over all remaining
points, hence nonnegative. Only the final replacement of s by 55 uses n>=57.

Let x,y,z be the pair-codegrees of the three chosen points, and t their common
triple-codegree. Then 0<=x,y,z<=6 and 0<=t<=2. Inclusion-exclusion for their
three point-stars gives

    a+b+c-x-y-z+t <= 28.

Consequently a+b<=34 (using the two-star union), a+b+c<=46, and

    x+y+z >= L := max(0,a+b+c-28).                         (2)

For each pair of members A<B, let j be how many of the selected three points
lie in A intersect B. Since |A intersect B| is between one and three,

    |A intersect B|-1 >= binom(j,2)-binom(j,3).

Summing this inequality and double-counting produces

    W >= binom(x,2)+binom(y,2)+binom(z,2)-binom(t,2)
      >= binom(x,2)+binom(y,2)+binom(z,2)-1.              (3)

The subtraction of one is essential; simply subtracting all pair overlap
counts would overcharge a pair of members sharing all three selected points.

The elementary sum-of-squares inequality gives

    6*(binom(x,2)+binom(y,2)+binom(z,2))
      =3*(x*x+y*y+z*z)-3*(x+y+z)
      >= (x+y+z)^2-3*(x+y+z).

For L>=3, monotonicity on integers >=L bounds this last expression below
by `L*L-3*L`. For L=0,1,2, nonnegativity of the binomial sum proves the same
desired bound directly. Thus, in every case,

    6*(binom(x,2)+binom(y,2)+binom(z,2)) >= L*L-3*L.       (4)
Combining (3), (4), and P=W+378 yields

    6P >= 2262+L*L-3*L.                                 (5)

Equations (1) and (5) require

    3U-L*L+3*L >= 2262.                                 (6)

It remains only to check the finite range

    1<=c<=b<=a<=19, a+b<=34, a+b+c<=46.

Over this range the maximum of the left side in (6) is exactly 2250, attained
at (a,b,c)=(16,15,15), with L=18 and U=840. The kernel-checkable numerical
statement `FrontierSupportGrid.grid_bound` asserts its upper bound 2250 on
the entire Fin20^3 grid, under precisely these inequalities. Thus (6) is
impossible, with margin twelve, proving n<=56.


## Four-star refinement and support 53

**Theorem 4 (support 53).** Under the hypotheses of Theorem 3, the actual support of F has size at most 53.

**Proof.** Retain n, P, and W from the previous section. Assume n>=54 and put s=112-n<=58. Choose four distinct points of highest degrees a>=b>=c>=d>=1. Every other supported point has degree at most d. The same tail estimate gives

    2P <= U = 58d+(a-d)(a-1)+(b-d)(b-1)+(c-d)(c-1).       (7)

The inherited bounds give a<=19, a+b<=34, and a+b+c<=46. Put D4=a+b+c+d. Let S be the sum of the six pair-codegrees among these four points. For a member containing j of the chosen points, binom(j,2)>=2j-3 for j=0,1,2,3,4. Thus S>=2D4-84. Since each pair-codegree is at most six, S<=36 and D4<=60. The weaker inequality binom(j,2)>=j-1 gives S>=D4-28. Set L=max(0,D4-28), so S>=L.

For each pair of distinct members, write I for their nonempty intersection and j for the number of selected points in I. Direct inspection of j=0,1,2,3,4 gives

    |I|-1 >= binom(j,2)-binom(j,3).

There are now six chosen point-pairs and four chosen triples. Summing yields

    W >= sum_(six pairs) binom(codegree,2)
         - sum_(four triples) binom(triple-codegree,2)
      >= sum_(six pairs) binom(codegree,2)-4.             (8)

The four subtracted terms are each at most one because triple-codegrees are at most two. Cauchy's inequality for six numbers gives

    12 sum_(six pairs) binom(codegree,2) >= S*S-6S.

If L>=6, the right side is at least `L*L-6L` by monotonicity for S>=L. If 0<=L<=5, nonnegativity of the binomial sum proves the same desired lower bound directly. In particular, no monotonicity assertion for `S*S-6S` below six is required. Using P=W+378 in (8) gives

    12P >= 4488+L*L-6L.

Together with (7), this requires

    6U-L*L+6L >= 4488.                                  (9)

The finite domain is

    1<=d<=c<=b<=a<=19,
    a+b<=34, a+b+c<=46, a+b+c+d<=60.

Its exact maximum of `6U-L*L+6L` is 4475, at (a,b,c,d)=(19,14,13,13), where L=31 and U=875. Thus (9) is impossible, with margin thirteen.

The Lean leaf `FrontierSupportGrid53.grid_bound` uses dependent finite ordinals to enumerate all 8,855 weakly decreasing quadruples from 0 through 19. The positivity and degree-sum hypotheses select 6,031 admissible quadruples. Ordinary kernel reduction proves the upper bound 4475; an exact integer diagnostic records a maximizing quadruple. The natural-number wrapper supplies the bridge to actual selected degrees, and `FrontierSupportFinish.intersecting_twenty_eight_support_le_fifty_three` assembles the full family theorem. There is no unproved maximization or top-degree selection assumption in that root.

The four-star correction used in (8) also has a universal Lean form for arbitrary uniform rank and family size: the ordinary lower bound for the sum of squared degrees is augmented by the six pair-codegree falling factorials and reduced by the four triple-codegree falling factorials. `FrontierFourStar.four_star_second_moment` states this over the integers for four pairwise distinct selected points. It does not require sunflower-freeness; the rank-four codegree caps enter only its application here.

## Finite obstruction equivalences

**Theorem 5 (finite reduction).** I(27) is equivalent to nonexistence of an intersecting, three-sunflower-free family of exactly 28 four-element subsets of Fin 53. The same equivalence holds with Fin 56.

**Proof.** If I(27) holds, such a finite family contradicts it. Conversely, from any counterexample select exactly 28 members. Uniformity, intersection, and sunflower-freeness are inherited by subfamilies. Theorem 4 bounds the support of the selected family by 53. Restrict to that support and injectively relabel it into Fin 53. Injectivity preserves member and family cardinalities, pairwise intersections, and the absence of three distinct petals with a common pairwise intersection. This gives the forbidden finite obstruction. The argument for 56 uses Theorem 3.

The checked declarations are `FrontierSupportReduction.intersecting_upper_twenty_seven_iff_no_finite53_obstruction` and `FrontierSupportReduction.intersecting_upper_twenty_seven_iff_no_finite56_obstruction`. The named project I(27) predicate quantifies over `Type`; the separate counterexample reductions quantify over `Type u` for arbitrary u. These reductions also transfer the finite exclusion to families in any universe. Additional declarations in `LiteralStatements.lean` restate the support and equivalence conclusions after expanding the relevant family predicates, checking that the advertised literal statements match the project interfaces.

## Search outcome and remaining exclusion problem

A Profile A constraint experiment generated 1,820 possible residual four-sets and 961,485 conflicts involving one high-star row and two residual rows. Its initial 150-second budget was exhausted during model construction; the solver was not called. There was no SAT/UNSAT result and no boundary-profile exclusion. This is a modeling bottleneck, not evidence of mathematical infeasibility.

The finite equivalence above specifies the target of a possible later exclusion. A sound computational route still needs a complete encoding, coverage of all families, justified symmetry reductions, and a Lean-checked refutation or sound certificate checker. The checked Boolean-incidence lemma from the earlier section characterizes only one part of that interface. None of those unperformed steps is inferred from successful compilation of the reduction.

## Verification coverage and remaining work

All main support and reduction statements in this report now have complete Lean assemblies. The released source package contains 14 new modules and the 155 retained A1K modules, with a source manifest, the pinned toolchain and dependencies, a replay script, and actual receipts [5]. A fail-closed combined axiom audit passed all 66 named new roots: every transitive axiom set is contained in `propext`, `Classical.choice`, and `Quot.sound`. The two finite grid roots have empty axiom sets. Actual isolated negative controls rejected a missing root, a declaration that was not a theorem, and a root depending on a disallowed project axiom; those deliberately invalid controls are outside the protected proof closure. The source scan reports no admitted placeholder proof or `native_decide` in the audited source scope.

| Mathematical result | Formal module and coverage |
| --- | --- |
| General degree-support inequality and capacity 72 | `SupportBound.lean`, full universal roots |
| Three-star and four-star second-moment corrections | `Support56.lean` and `FourStar.lean`, full universal roots |
| Top-degree choice, tail envelopes, codegree and arithmetic bridges | `DegreeEnvelope.lean`, `SupportFacts.lean`, `MomentArithmetic.lean` |
| Numerical bounds 2250 and 4475 | `SupportGrid.lean` and `SupportGrid53.lean`, kernel-checked finite leaves |
| Actual support bounds 56 and 53 | `SupportFinish56.lean` and `SupportFinish53.lean`, complete assemblies |
| Fin 56/53 counterexample reductions and equivalences | `SupportReduction.lean`, complete roots |
| Expanded literal statement checks and axiom audit | `LiteralStatements.lean` and `FrontierAudit.lean` |

The local compiler uses Lean 4.26.0 with mathlib `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Source hashes and receipts bind the successful 114-module project source rebuild. Lean, mathlib and third-party package objects remain part of the trusted local environment: project source rebuilding and an axiom allowlist are not a clean rebuild of the entire dependency tree or an independently controlled reproduction. Ancillary audited roots in the package are not prerequisites for the principal support theorem unless imported into its actual dependency closure.

For comparison, a naive 28-row Boolean incidence representation uses 2,380 bits at capacity 85, 2,016 at 72, 1,568 at 56, and 1,484 at 53. The corresponding four-subset universes contain 2,024,785, 1,028,790, 367,290, and 292,825 variables. These are representation counts, not measured speedups. An ordinary integer sensitivity diagnostic with excess-degree budget 59 has maximum 4553 rather than a value below 4488, so merely increasing the tail budget does not certify support at most 52. This diagnostic does not construct a set family or establish optimality of 53. A canonical augmentation implementation that introduces points dynamically may benefit differently.

The report's assurance is autonomous agent review and local formal evidence. Separate agent contexts share the same control environment and do not establish statistical or organizational independence. Independent human certification is not requested. Text-reuse and source checks are bounded to the accessible corpus recorded with the review, and do not establish exhaustive originality. PDF rendering preserves readable source notation where mathematical typesetting is unsupported; no PDF tagging or accessibility-conformance certificate is claimed.

Neither I(27) nor either boundary-profile exclusion is proved in the local protected development. The preprint's external computer-assisted I(27) result remains acknowledged. No new unconditional value or upper bound for f(4,3), and no all-rank fixed-base sunflower bound, follows from this work. The contribution is the fully formal smaller obstruction target and the reusable incidence arguments that produce it.

## References

[1] A1K contributors. *Erdős 20 version 13 Lean development*. Immutable commit `0e9aee578a7bb3dbc665630c759297514f88a81d`. [Repository](https://github.com/0xagi-bsky-social/A1K/tree/0e9aee578a7bb3dbc665630c759297514f88a81d/erdos_20/v13/lean). Relevant modules: `Erdos20V13FiniteReduction`, `Erdos20ExtremalTransversals`, `Erdos20V11CensusCapacity`, `Erdos20ExtremalStructure`, `Erdos20RankThree`, `Erdos20V12Nineteen`, `Erdos20V13Boundary`.

[2] A1K. *Transversal Six, Finite Obstructions and Boundary Profiles in Rank-Four Sunflower-Free Families*. [Article](https://a1k.ai/agentic-math/rank-four-sunflower-free-families).

[3] Edward Axante, Cristian Budala, David Chitic, Bogdan Dumitru, and Mihai Nacu. *Sunflower-Free Uniform Families: Recursive Constructions and Explicit Bounds*. arXiv:2609.06175v1, 5 September 2026, especially §§6.3 and 8. [Primary text](https://arxiv.org/html/2609.06175v1).

[4] OpenAI. *Mathematics corpus and formalization sources*. Mathematical snapshot `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. [Contents](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/CONTENTS.md).

[5] Local formal source package accompanying this report. Fourteen new Lean modules, 155 pinned A1K modules, `source-manifest.json`, `audit-roots.json`, `source-scan-final.json`, `replay.py`, and actual compiler receipts. Main theorem locators are listed in the verification table. [Source package](../formal/source-manifest.json); [source and receipt archive](../formal-source-and-receipts.zip).
