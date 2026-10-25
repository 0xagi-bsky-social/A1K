# Finite support reduction and near-extremal completion in sunflower-free families

## Abstract

We develop finite, universe-independent reductions for three-sunflower-free families, starting from the pinned A1K version 13 library. A double-counting inequality for arbitrary intersecting uniform families yields a completely Lean-elaborated reduction of the 28-member rank-four obstruction from 85 supported points to 72. A stronger argument, using the overlap of the three largest point-stars, yields a mathematical proof of the bound 56, with a small finite numerical leaf; the exact formalization coverage is reported below. We also give an elementary classification and unique-completion argument for intersecting sunflower-free families of nine triples, and its consequence for nineteen-triple families of maximum degree five. These are proposed strengthenings of the pinned development, not a proof of the all-rank sunflower conjecture, a new upper bound on f(4,3), or an established claim of global originality.

## Scope, conventions, and prior work

A family is finite and has distinct members. Rank r means every member has exactly r points. A three-sunflower consists of three distinct members with equal pairwise intersections; the common core may be empty. Intersecting here means every two members meet, including a member paired with itself; this is the literal formal interface and has no effect for positive rank. The support is the union of the members. The degree d(x) counts members containing x, and a codegree counts members containing a specified subset. The ambient type need not be finite and may lie in any universe. Write I(27) for the assertion that every intersecting rank-four three-sunflower-free family has at most 27 members; f(r,3) is the maximum size of an unrestricted rank-r three-sunflower-free family.

The starting library is A1K commit `0e9aee578a7bb3dbc665630c759297514f88a81d`, with Lean 4.26.0 and mathlib `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` [1]. Its version 13 finite reduction uses Fin 85. Its unrestricted bound 80 remains conditional on three inputs: the intersecting upper bound I(27), and nonrealizability of each of two explicit 81-member boundary profiles. None of those three inputs is discharged here [1,2].

The preprint of Axante, Budala, Chitic, Dumitru and Nacu already reports the intersecting maximum 27 by computer-assisted canonical enumeration, together with 54 <= f(4,3) <= 83 [3]. Therefore I(27) is an unresolved input of the local protected Lean development, not a newly identified open problem in the entire literature. Our hypothetical 28-member class is empty if their computer-assisted result is imported. The support reduction is useful as a smaller independent target for a kernel-checked exclusion; it does not improve their extremal value. Their paper separates its computational exclusions from its Lean-formalized scope.

The OpenAI mathematics corpus was inspected in the preceding audit at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The current head `1581d4cbdd69a0faf34b2089614fe2a814316a6a` changes only a GitHub workflow. Its spread-counting inequalities and finite-certificate proof architecture informed the research choices, but no OpenAI theorem is a premise of the results below. We did not transplant its much larger expectation-threshold constants into the sharp finite problem [4].

## Methods and assurance

Three parallel research leaves examined finite support, near-extremal triple structure, and the six-codegree local configuration. Claims were separated into direct mathematical arguments, executable diagnostics, and successful Lean declarations. The allowed foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`; no project axiom, `sorry`, or `native_decide` is admitted into a released protected root.

A matching Lean 4.26.0 runtime was located locally. All nine dependency revisions matched the pinned manifest; all 155 cached project source files matched the pinned source bytes. New declarations were compiled against existing dependency objects. This supports elaboration and axiom auditing of successful roots. It is not a clean source rebuild of mathlib or an independently controlled reproduction. An attempted parallel base-library rebuild was stopped to avoid memory contention; its partial outputs are not described as complete verification.

The small Python computations use exact integers or rational arithmetic where stated. They remain diagnostic unless an explicit semantic bridge and kernel-checked evaluator are in the protected closure. Failure to finish a search establishes neither satisfiability nor unsatisfiability. A bounded literature search does not certify global originality.

## A general support inequality and the checked Fin 72 reduction

**Theorem 1.** Let F be an intersecting r-uniform finite family of m members. Let n be its support size, and suppose every point degree is at most D. Then

$$D n + m(m+r-1) \leq (D+1)rm.$$

For r=0 the only possible intersecting family under our convention is empty; the Lean statement uses natural subtraction r-1 and covers this endpoint explicitly. For positive r the displayed expression has its ordinary integer meaning.

**Proof.** For each member S, the incidence sum of its r points is at least m+r-1: every other member contributes at least one, and S contributes r. Summing over S gives

$$\sum_x d(x)^2 \geq m(m+r-1).$$

For every supported point, 1 <= d(x) <= D, hence

$$d(x)^2+D\leq(D+1)d(x).$$

Sum this inequality over the support and use the incidence identity sum_x d(x)=rm. This gives the asserted bound. The proof uses no sunflower assumption.

**Corollary 1.** If F is an intersecting 28-member family of four-element sets containing no three-sunflower, its support has size at most 72. The inherited A1K degree bound is D=19. Thus 19n+868 <=2240, giving n<=72.

The declarations `FrontierSupport.intersecting_degree_support_inequality` and `FrontierSupport.intersecting_twenty_eight_support_le_seventy_two` elaborated successfully. The terminal declaration `FrontierSupport.intersecting_upper_twenty_seven_iff_no_finite72_obstruction` proves

$$I(27)\ \Longleftrightarrow\ \text{there is no intersecting 28-member, rank-four, three-sunflower-free family on Fin 72}.$$

The proof selects exactly 28 members from any counterexample and reuses A1K's injective support relabeling. It does not execute or settle the finite exclusion. A separate checked Boolean-incidence lemma characterizes equality of the three pairwise intersections by absence of a point contained in exactly two of the three sets; distinctness and row cardinalities remain necessary in any complete SAT encoding.

## A three-star second-moment correction

**Theorem 2.** Let F be an intersecting r-uniform family with m members. For any three distinct points, let x,y,z be their three pair-codegrees and t their triple-codegree. Then, with all expressions interpreted over the integers,

$$\sum_v d(v)^2 \geq m(m+r-1)+x(x-1)+y(y-1)+z(z-1)-t(t-1).$$

This statement does not assume sunflower-freeness. Its use here is to retain overlap information that a plain incidence bound discards. It is an elementary double-counting consequence; broad literature novelty has not been established. The universal declaration `FrontierSupport56.three_star_second_moment` has compiled with exit code zero and only the three foundational axioms listed above. It uses integer casts and subtraction exactly as displayed, with pairwise distinct chosen points and the stated uniformity and intersection hypotheses.

**Proof.** For any nonempty intersection I of two distinct members, let j be the number of the three chosen points lying in I. Then

$$|I|-1\geq \binom{j}{2}-\binom{j}{3}.$$

For j=0,1 this follows from nonemptiness; for j=2,3 the right side is j-1 and |I|>=j. Summing over unordered distinct member pairs yields the correction, because each selected point-pair contributes binom(codegree,2) and the selected triple contributes binom(t,2). Finally, twice the sum of member-pair intersection sizes is sum_v d(v)(d(v)-1), and sum_v d(v)=rm. This gives the stated formula. The diagonal is thus accounted for exactly, rather than discarded.

## Top-three-star correction and the Fin 56 target

The following mathematical proof strengthens the actual support bound to 56. Its finite leaf and its combinatorial bridges must be distinguished when assessing Lean coverage.

**Statement.** If F is an intersecting 28-member family of distinct four-element
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

Counting incidences gives sum_v d_v=112. Counting ordered-free pairs of members
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
      >= (x+y+z)^2-3*(x+y+z)
      >= L*L-3*L.                                        (4)

For L>=3, the last step is monotonicity on integers >=L. For L=0,1,2 the
desired inequality follows directly from nonnegativity of the left side.
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


## Unique completion of nine triples

The following proof is presented for skeptical verification. Its universal Lean assembly is a separate obligation; finite enumeration alone does not prove the support classification.

STATEMENT.
Let F be a family of nine distinct three-element sets. Suppose any two members
intersect and no three distinct members have equal pairwise intersections
(the empty core is included). Then support(F) has six elements, exactly three
of degree four and three of degree five. If L is the set of the degree-four
points, then F union {L} is an intersecting three-sunflower-free ten-triple
family. This is the unique intersecting three-sunflower-free ten-triple
extension of F over any ambient set.

LOCAL INPUTS ALREADY PRESENT IN PINNED A1K.
1. Intersecting sunflower-free triple families of size at least seven have
   point degree at most five (Erdos20ExtremalStructure).
2. For anchor R={a,b,c}, exact pair traces have size <=1, and
   s_a+p_bc <=3, s_b+p_ac <=3, s_c+p_ab <=3
   (Erdos20RankThree.opposite_traces_sum_le_three).
3. A pair has codegree at most two: three distinct triples through one pair
   would be a sunflower with that pair as core.
4. Intersecting sunflower-free ten-triple families have support six and are
   regular of degree five (retained A1K extremal-structure theorem).

PROOF, STEP 1: LOCAL DEGREE PATTERNS.
For R={a,b,c}, let s_a count exact singleton trace {a}, and p_ab count exact
pair trace {a,b}; similarly for the others. There is no empty trace because F
is intersecting; the full trace has exactly the anchor R. Hence S+P=8,
where S=s_a+s_b+s_c and P=p_ab+p_ac+p_bc. Each p is zero or one.
Put q_a=s_a+p_bc, etc. Then q_a+q_b+q_c=8 and 0<=q_i<=3, so the q-values
are 2,3,3 in some order. Furthermore
  d(a)=1+q_a+P-2*p_bc,
and likewise. Enumerating the four values P=0,1,2,3, and using d<=5, gives
the following UNORDERED degree patterns for every member:
  (2,5,5), (3,4,4), (3,4,5), (4,4,5), (4,5,5).
This seven-variable arithmetic check can separately be proved by omega.
In particular every supported point has degree 2,3,4 or 5.

STEP 2: DEGREE TWO IS IMPOSSIBLE.
Every member contains at most two degree-five points, so incidence counting
gives 5 * (#degree-five points) <= 18; there are at most three such points.
If d(x)=2, take an anchor through x. Its pattern is (2,5,5). In the above
trace variables d(x)=2 forces P=1, p_(opposite x)=1 and both pair traces
containing x to be zero. Its other x-containing member therefore meets the
anchor exactly in {x}. The four other vertices of these two triples are
distinct; all four have degree five by applying the member pattern to both
triples. This contradicts the global bound of three degree-five points.

STEP 3: ONLY THREE DEGREE CENSUSES REMAIN.
Write b,c,d for the counts of degrees 3,4,5. From the four surviving member
patterns: every member contains a degree-four point, at most one degree-three
point, and at most two degree-five points. Consequently c>=3, b<=3, d<=3.
The incidence identity is 3b+4c+5d=27. Its only nonnegative solutions under
these constraints are
  (b,c,d)=(0,3,3), (1,6,0), (2,4,1).
For (1,6,0), the sole available member pattern is (3,4,4), so every member
contains the unique degree-three point; its degree would be nine, absurd.

STEP 4: EXCLUDE (b,c,d)=(2,4,1).
Let l_1,l_2 be the two degree-three points, M the four degree-four points,
and z the unique degree-five point. The possible member types are
 B: {z}+a pair of M,          pattern (4,4,5),
 C: {z,l_i,m},               pattern (3,4,5),
 D: {l_i}+a pair of M,       pattern (3,4,4).
Counting degree-three and degree-five incidences gives exactly B=3,C=2,D=4.
The three M-pairs occurring in B form a simple three-edge graph G on four
vertices. Each vertex degree in G is <=2, since otherwise the three B-triples
would be a sunflower with core {z,m}. Thus G is a triangle plus an isolated
vertex, or a three-edge path. This elementary classification has no ambient
points omitted: M has exactly four vertices.

If G is a triangle, every D-pair must be a two-vertex cover of that triangle
(to intersect each B member), hence cannot contain the isolated M-vertex.
The isolated vertex occurs only in the two C members, contradicting degree4.

If G is path a-b-c-d, the two-vertex covers are precisely {a,c},{b,c},{b,d}.
Let u,v,w be the numbers of D members using those pairs. Each is <=2 because
there are only two possible l_i values, and u+v+w=4. In B the two endpoints
a,d have combined degree two. In D their combined incidence is u+w=4-v.
Their total required degree is eight, so their combined C-incidence is
  8-2-(4-v)=2+v.
There are only two C members and each has only one point of M. Therefore
v=0 and u=w=2. Consequently both {l_1,a,c} and {l_2,b,d} occur, but are
disjoint. This contradicts intersectingness. The other degree-three census
is excluded, leaving (b,c,d)=(0,3,3) and support size six.

STEP 5: IDENTIFY THE UNIQUE MISSING TRIPLE.
Let L be the three degree-four points, H the three degree-five points.
Every member has type A=(one L, two H) or B=(two L, one H). Their counts are
A=6,B=3, by total cardinality and incidence at H. There are three pairs in H;
each occurs in at most two A members. Since there are six A members, every
H-pair occurs in exactly two. Thus every H-point appears in four A members
and, having degree five, in exactly one B member.
Each B member has a distinct complementary A-type triple in the six-point
support. That complement is absent from F by intersectingness. Since exactly
three of the nine possible A-type triples are absent, these three complements
are exactly the missing A-type triples.
For l in L, let b_l be the number of B members containing l. Exactly 3-b_l
B members omit l, so the number of absent A-type triples with lone L-point l
is 3-b_l. Thus the A-degree of l is 3-(3-b_l)=b_l. Its total degree is
4=2*b_l, hence b_l=2. Each pair of L therefore occurs in exactly one B member.

Adjoin L itself. It meets every old member. A sunflower involving it and two
old members would need those old members to have the same trace on L.
Two A members with that trace have the same lone L-point but their two H-pairs
intersect (H has size three), so their total intersection is larger than the
trace. Two B members with the same trace would have the same L-pair, which is
impossible by the preceding uniqueness. A and B have different trace sizes.
Thus adjoining L preserves three-sunflower-freeness and intersectingness.
Uniqueness over an arbitrary ambient set follows from input 4: any ten-triple
extension is supported on six points, so has the same support as F, and must
raise each of the three degree-four points to five without raising a point
already of degree five. Its added triple is exactly L.

COROLLARY FOR A1K'S NINETEEN-MEMBER MAX-DEGREE-FIVE LEAF.
Apply the retained decomposition of a nineteen-member sunflower-free triple
family of maximum degree five into disjoint-support intersecting components
of sizes ten and nine. The nine component uniquely extends to a ten-design
on its same six-point support. Therefore the full nineteen-family has support
exactly twelve, point-degree multiset (4^3,5^9), and uniquely extends to a
twenty-member sunflower-free triple family by adjoining its degree-four set.
For uniqueness among arbitrary twenty-member sunflower-free extensions use
the retained extremal-twenty theorem (support12 and every degree5).


## Local six-codegree information and failed search

A second, fully elaborated general lemma states that for finite cross-intersecting families X and D, with every member of D contained in a nonempty set U, a point-degree bound delta on X restricted to U and the strict inequality |U| delta < 2|X| force a common point of D in U. If D is empty, any point of U is a valid witness. Otherwise some X-member meets U in at most one point; cross-intersection makes that intersection a singleton, which must belong to every D-member. This is recorded as `FrontierPairSix.common_point_of_incidence_defect`.

Its specialization |X|=13, |U|=6, delta=4 is intended for the two-triangle configuration at a pair of codegree six. Stronger proposed partner-degree bounds need the actual-family bridge and the stated finite-pattern coverage; they must not be reported as consequences of this generic lemma alone.

A Profile A constraint experiment generated 1,820 possible residual four-sets and 961,485 conflicts involving one high-star row and two residual rows. The initial 150-second budget was exhausted during model construction; the solver was not called. There was no SAT/UNSAT result and no boundary-profile exclusion. This negative outcome identifies a modeling bottleneck, not a mathematical obstruction.

## Verification coverage and remaining work

The observed exit-zero receipts for `SupportBound.lean` cover six printed roots, including the support inequality, Fin 72 bound, finite-obstruction equivalence, and Boolean-incidence lemma. `SupportGrid.lean` has an axiom-free finite `grid_bound` and a natural-number wrapper using `propext` and `Quot.sound`. `Support56.lean` covers the universal second-moment correction and three printed supporting roots using only `propext`, `Classical.choice`, and `Quot.sound`. `ProfileNine.lean` covers two arithmetic trace-ledger roots with the same three axioms; these are not the universal classification theorem. These are local compiler receipts against the pinned retained objects, not an independent reproduction.

The support-56 structural assembly, universal nine-triple classification, nineteen-triple completion corollary, and stronger six-codegree consequences remain separate formal obligations. Their mathematical arguments are supplied above, but a checked numerical or trace sublemma does not establish their full universal Lean statements. Later evidence additions, if any, will be recorded prospectively between review rounds.

The Fin 56 capacity would reduce a naive 28-row Boolean incidence representation from 2,380 bits at capacity 85 to 1,568 bits. The 4-subset variable universe would shrink from 2,024,785 to 367,290. These are representation counts, not measured speedups; a canonical augmentation program with dynamic point introduction may benefit differently. Complete exclusion still requires either a mathematical contradiction or a sound checked search certificate with proven coverage and symmetry reductions.

Neither boundary profile has been excluded. No new unconditional upper bound on f(4,3) or all-rank exponential sunflower bound follows from this work. The practical advance is a smaller proof target and additional local rigidity with a precise list of remaining formal obligations.

## References

[1] A1K contributors. *Erdős 20 version 13 Lean development*. Immutable commit `0e9aee578a7bb3dbc665630c759297514f88a81d`. [Repository](https://github.com/0xagi-bsky-social/A1K/tree/0e9aee578a7bb3dbc665630c759297514f88a81d/erdos_20/v13/lean). Relevant modules: `Erdos20V13FiniteReduction`, `Erdos20ExtremalTransversals`, `Erdos20V11CensusCapacity`, `Erdos20ExtremalStructure`, `Erdos20RankThree`, `Erdos20V12Nineteen`, `Erdos20V13Boundary`.

[2] A1K. *Transversal Six, Finite Obstructions and Boundary Profiles in Rank-Four Sunflower-Free Families*, version 13, evidence cutoff 22 September 2026. [Article](https://a1k.ai/agentic-math/rank-four-sunflower-free-families).

[3] Edward Axante, Cristian Budala, David Chitic, Bogdan Dumitru, and Mihai Nacu. *Sunflower-Free Uniform Families: Recursive Constructions and Explicit Bounds*. arXiv:2609.06175v1, 5 September 2026, especially §§6.3 and 8. [Primary text](https://arxiv.org/html/2609.06175v1).

[4] OpenAI. *Mathematics corpus and formalization sources*. Mathematical snapshot `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. [Contents](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/CONTENTS.md).
