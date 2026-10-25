# Degree-18 structural tools at the 68-member target

23 October 2026. Working mathematical research, not a final review or a
publication step. Only ordinary arguments and source inspection are used here;
no solver, Lean, or classification job was run. The ambient support is arbitrary.

Let F be a finite simple four-uniform family with no three distinct members
having equal pairwise intersections, including empty core. Write R for the
members avoiding a distinguished point x. At degree 18 and |F|≥68, r=|R|≥50.
H27 denotes the imported bound 27 for intersecting sunflower-free four-uniform
families. A global maximum-degree cap 18, when invoked, is a separate premise;
it does not follow merely from the existence of one degree-18 point.

## A stronger ordinary terminal separation lemma

Suppose F contains all cones x∪T for T in H_Y∪H_Z, where H_Y and H_Z have
disjoint supports Y and Z and every subset of either support of size at most
two misses some block of the corresponding component. P9 and P10 satisfy this
condition: P10 has exactly two blocks avoiding any given pair, and deleting
one block leaves at least one. Put S=Y∪Z. The following statements need only
these prescribed cones; their completeness is not needed for this lemma.

**Small union criterion.** If two residual members Q,Q′ are disjoint, then
`(Q∪Q′)∩Y` must meet every block of H_Y, and `(Q∪Q′)∩Z` must meet every block
of H_Z. Otherwise a missed block T gives a cone x∪T disjoint from both Q and
Q′, producing three distinct disjoint members. The cone is distinct because
it contains x, and Q≠Q′ because nonempty disjoint four-sets are distinct.
In particular, disjoint residuals have at least three points in each component
in their union, hence at least six link-support points altogether.

The general form uses the transversal numbers τ_Y,τ_Z: a disjoint residual
pair has at least τ_Y+τ_Z support points in its union. Thus the at-most-two
trace conclusion below also holds whenever τ_Y+τ_Z≥5. In the other degree-18
link form P10⊔I8, P10 has transversal number three and I8 has transversal
number at least two (a one-point transversal would be a point of degree eight
in SF3, exceeding the universal point-degree bound six). Therefore an eventual
at-most-two-support-point reduction also makes all residuals intersecting in
that branch, even when I8 is Q8 on seven points.

**At most two link points per residual.** If every residual has at most two
points in S, no disjoint residual pair exists: its union would have at most
four S-points. Thus R is intersecting, and H27 gives

    r≤27.

No exclusion of mixed two-point traces is needed for this conclusion. More
generally, if every residual has at most three S-points, each residual with
at most two S-points intersects every residual, since their union has at most
five S-points.

**Pure-triple terminal geometry.** Assume every residual trace is either of
size at most two, or is a three-set contained wholly in Y or wholly in Z.
Call a pure triple a transversal if it meets every block of its component.
Let T_Y and T_Z be the actual residual subfamilies whose traces are such pure
transversal triples in Y and Z, respectively. Then every disjoint pair of
residuals consists of one member of T_Y and one member of T_Z.

Indeed the small union criterion first forces both traces to have size three.
Two pure triples in the same component leave the other component empty in
their union, impossible. For opposing pure triples U⊆Y and V⊆Z, if U is not a
transversal, choose a Y block avoiding U. Its cone also avoids the Z trace V
and all exterior points, so it is disjoint from both residuals. This is again
an empty-core sunflower. The same reasoning applies to V. Thus each trace
must be a transversal of its own component, independently of the other one.

Consequently both R\T_Y and R\T_Z are intersecting. Under H27,

    r≤27+min(|T_Y|,|T_Z|).                         (TS)

This formulation permits mixed pair traces. A known absence of all mixed
pairs is stronger than needed. If one side has no pure transversal residuals,
the entire residual family is intersecting and r≤27.

### Immediate consequences for the active branches

For a P9 component obtained from P10 by removing a block B, the eleven
three-point transversals are the nine surviving blocks, B, and its complement
C in the six-point component. Each surviving block has at most one residual
extension, because its cone already uses one of the universal triple-codegree
capacity two. The two complementary exceptional triples together have at most
two extensions under the pure-triple terminal geometry.

To prove the last statement, write their residual extensions as B∪{a} and
C∪{b}, with a,b outside {x}∪S. If a≠b these two members are disjoint, as is
any cone on the other component, impossible. If both exceptional families are
nonempty, all their extension points are therefore equal, and simplicity
allows exactly one extension of each. If one is empty, triple codegree bounds
the other by two. Hence |T_Y|≤11 for a P9 side; the same holds for Z.

Thus the R99 terminal geometry gives the stronger ordinary bound

    r≤38,       |F|≤18+38=56,                    (R99-terminal)

in place of the older cone-disjointness bound `10r≤508`. This is a conditional
terminal result: the old μ42-based internal and mixed-triple exclusions have
not thereby been proved at the new target. Their geometric conclusions must
first be obtained with valid size-68 premises.

For the active D19 terminal described by the parent task, all residual traces
have size at most two except possibly pure Z triples (in particular the
surviving E22/E26 cases); there are no pure Y triples. Provided those exclusions
have been established, T_Y is empty, and the residual family itself is
intersecting. H27 gives r≤27 and |F|≤19+27=46. The argument does not require
the surviving Z triples to be classified or removed.

For the D20 terminal with at most two link points per residual, the same
reasoning gives |F|≤20+27=47. These conditional bounds are not claims about
arbitrary degree-18, degree-19, or degree-20 families before the trace
restrictions have been proved.

## Scope of the source transfer

The frozen D18_P10 and D18_R99 proofs contain reusable geometric lemmas but
also finite exclusions under μ42 and the old target r≥51. Those exclusions
are not imported here as valid at r≥50. H27 alone gives |N[A]|≥|F|−27≥41 for
every actual anchor A. It does not supply μ42, a positive minimum degree,
an upper support bound, or old minimum degree-sum constraints.

Further source-safe inequalities and the constructor notes follow below.

## Complete exterior singleton families and central-anchor states

Fix one P10/P9 component S, a point y∈S, and an actual central anchor
R=x∪T with y∈T. In the complete triple link L_y let A=R\{y}, let D be the
members disjoint from A, and let K be those meeting A. Write s=|D|, k=|K|.
Let

    H_y={H:H∩({x}∪S)=∅, {y}∪H∈F},     h_y=|H_y|.

This H_y is the exact component-singleton coordinate n_{ {y} }, not the exact
singleton coordinate at the smaller four-point anchor. Always H_y⊆D, so
h_y≤s. The following lower bounds also hold:

    h_y≥ell(s),  ell(8)=6, ell(9)=9, ell(10)=10,
    ell(s)=0 for 0≤s≤7.                              (EXT)

**Proof, with the Q8 core/leaf distinction.** The family D is intersecting:
two disjoint members of D together with the actual link anchor A would be a
three-sunflower with empty core. It is also SF3. At sizes 9 and 10, imported
intersecting classification makes D a P9 or P10. Every D member avoids A,
so its entire six-point support avoids A. By P-type isolation, a member of K
meeting that support would have to be one of the deleted P10 blocks. Such a
block also avoids A and would belong to D instead, contradiction. Thus K
avoids the whole support of D. The prescribed C5/P5 star in K covers all of
{x}∪(S\{y}); therefore D avoids this whole set, and h_y=s.

At s=8, a P8 gives exactly the same argument and again h_y=8. The remaining
case is D=Q8. Its five-point core avoids A. Isolation permits only the two
exceptional triples consisting of one hub and the two leaves to meet that
core from outside Q8. All seven Q8 points avoid A because every Q8 point is
used by D; thus both exceptional triples also avoid A. They cannot lie in K.
Consequently K avoids the Q8 core. Since K's prescribed star covers
{x}∪(S\{y}), the core is wholly outside that set. All six Q8 triples supported
on the core are members of H_y, yielding h_y≥6. Its two leaf triples may meet
S at their leaves. This proof does not assert that the leaves are isolated or
that h_y=8 in the unrestricted Q8 case.

There is no arbitrary-I7 classification in this proof: only the imported
classification at s=8,9,10 is used.

### When equality h_y=s is available

At a C5 neighbor with d(y)≥16, the complete-C5 structural lemma in
`C5-internal-compatibility.md` gives two intersecting components on disjoint
supports, with the x-component containing all of {x}∪(S\{y}). Its other
members cover the cycle and are internal. The opposite component is exactly
D and is wholly exterior to S. Conversely every member of H_y is disjoint
from A and belongs to D. Hence h_y=s at every central anchor through y.

At a P5 neighbor with d(y)≥17, the universal high-link theorem gives the same
disjoint-support partition. The x-component contains the full four-edge path,
hence all of {x}∪(S\{y}). Its possible exterior additions still contain the
unique two-point path cover and therefore are not members of H_y. The opposite
component is precisely H_y=D. Again h_y=s. The degree-17 x-component may have
seven members; this argument does not classify that arbitrary I7.

There is a further safe equality case: if K is known to be intersecting and
k≥8, then h_y=s. The I8/I9/I10 classification applies to K. K cannot be Q8:
the complete point-link at x is C5 or P5, whereas Q8 point-links are a triangle
with two additional hub–leaf edges, a four-cycle, or a single edge, none equal
to C5 or P5. Thus K is a P-type. Its six-point support already contains all
six points of {x}∪(S\{y}), so the supports are equal. P-type isolation forces
D to avoid that support: a deleted block would meet A because every P10 block
meets the actual P-type block A, contradicting membership in D. This proves
equality. In particular it applies when s≥8 and k≥8, since B4 supplies the
required intersecting K.

**Caution at s≤7.** The numerical condition k≥8 alone does not establish that
K is intersecting. B4 supplies this only at s≥8, and the stated high-degree
theorems supply it in their own ranges. No unconditional `h_y≥s−2` for s≤7
has been proved here. If an intersecting isolated P8/P9 near component is
actually known, the stronger equality h_y=s holds. It is unsafe to infer that
near-component hypothesis just from its cardinality k.

### Safe convex rows

For each central anchor through y with selector weights λ_r, use

    h_y ≥ sum_r λ_r g(r),

where g(r)=s_y(r) in either established high-degree equality regime, or when
the row has s_y(r)≥8 and k_y(r)≥8; otherwise g(r)=ell(s_y(r)). Every actual
family chooses one actual row, so this inequality is valid before relaxing
the selectors. The existing exact trace equations already give the matching
upper inequality h_y≤sum_r λ_r s_y(r). These rows use the same h_y in every
anchor through y and are therefore stronger than separate local bounds.

## H27 singleton pools and stronger affine pool bounds

For one P10/P9 component S put P_S=Σ_{y∈S}h_y. The actual four-sets counted
by these six categories form an intersecting SF4 family. Two members in the
same category share y. If members in different categories y,z were disjoint,
a component block avoiding y,z exists, and its cone would be disjoint from
both. H27 therefore gives

    P_S≤27.                                           (POOL)

This requires neither empty internals nor a second component of any specified
type. It counts all exterior completions, with multiplicity in each exact
trace coordinate. It is not a statement that arbitrary unions of other trace
categories are intersecting.

Each triple family H_y is itself intersecting SF3: two disjoint tails and a
prescribed cone through y would form a sunflower with core {y}. Hence h_y≤10.
The H_y are pairwise cross-intersecting by the same cone-avoiding-two-points
argument. A triple can occur in at most two of the H_y, because three different
centres adjoined to it would form a sunflower with that triple as core.

If h_y=10, classification gives a P10 tail family. Every other tail must be a
three-point transversal of it. P10 has no two-point transversal and exactly
its ten blocks as three-point transversals, so all tail families use these
ten triples and multiplicity at most two gives P_S≤20. If h_y≥9, choose a
P9 subfamily of H_y. Its eleven three-point transversals and absence of a
two-point transversal similarly give P_S≤22. These arguments allow arbitrary
exterior labels; any outside point in a transversal would leave a forbidden
transversal of size at most two on the six-point support.

Besides the direct implications, a useful universally valid linear row is

    2P_S+7h_y≤110               for every y∈S.          (POOL-affine)

For h_y≤8 this follows from P_S≤27; at h_y=9 it gives at most 107, and at
h_y=10 at most 110. Another selector form, at any central anchor through y,
is

    P_S + 5 Σ_r λ_r [s_y(r)=9]
        + 7 Σ_r λ_r [s_y(r)=10] ≤27.

Its validity uses h_y=s_y for s_y=9,10 as proved above; it is one row for each
point/anchor and must not be strengthened by summing different point penalties
without a further argument.

At the 68-member target at most one h_y can equal ten. If two do, their two
P10 tail families coincide by cross-intersection and the P10 transversal
description. The family then contains a doubled P10. The ordinary isolation
and counting proof in `doubled-P10.md` gives

    |F|≤27+d(y)+d(z)−d(y,z)≤27+2Δ,

where Δ is a global point-degree cap. Even the universal Δ≤20 gives at most
67; with Δ≤18 the bound is at most 63. Thus a selector constraint permitting
at most one complete-tail state h_y=10 is safe in a hypothetical F≥68.

## Pair traces consume singleton capacity

Fix y in a P10/P9 component S. Write a pair-trace member as `{y,j}∪E`, where
E is an exterior two-set. For a C5 neighbor take all these members and denote
their number by b. For a P5 neighbor with unique two-point path cover {a,b′},
take separately the subfamily with j≠a and the subfamily with j≠b′. Each
subfamily has its own count b and obeys the following table with h=h_y:

| b | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---:|---:|---:|---:|---:|---:|---:|
| h at most | 10 | 10 | 8 | 5 | 4 | 2 | 1 |

Here is a complete resource proof. The exterior edges E are pairwise
intersecting. For different partner points j,k, a star edge avoiding j,k
exists: a C5 has no two-cover, while the selected P5 subfamily cannot contain
both elements of its unique two-cover. If two exterior edges were disjoint,
the corresponding cone and two pair members would form a sunflower with core
{y}. With j=k use a cone through y,j instead, giving core {y,j}. Every tail
H∈H_y meets each edge E, using a cone through y avoiding j to rule out a
disjoint H,E. An exterior edge E occurs at most twice, by the triple codegree
bound on {y}∪E.

An intersecting simple edge family is a star or a triangle. For a star with
centre v, all b pair members consume the codegree capacity six of {y,v}, so
b≤6. For a triangle, each of its three edges has multiplicity at most two,
again b≤6. Every transversal H of the triangle uses at least one of its three
edges; summing the triple-codegree capacities on y plus those edges gives
b+h≤6.

In the star case with at least two distinct leaves, at most two singleton
tails avoid the centre, since each must contain those two leaves and their
joint triple with y has codegree at most two. At most 6−b tails contain the
centre, giving h≤8−b. If b≥5 there are at least three distinct leaves, since
each edge occurs at most twice. At most one tail then avoids the centre, by
simplicity of the three-element tail, giving h≤7−b. With a single distinct
edge uv, b≤2 and every tail meets u or v. Summing the two pair-codegree bounds
on {y,u},{y,v} gives h+2b≤12. Combining these facts with h≤10 gives the table.

The compact affine consequences used in the current constructor are

    b≤6,                 5h+9b≤59.                    (PAIR)

They follow by substituting the seven possible integer b values. The full
integer table is stronger at b=3: the affine rows alone permit h=6, while
the valid table gives h≤5. A mode split or integer pruning may use that fact;
a single additional linear inequality valid on all modes cannot simply cut
away that point, which lies below the upper convex hull of the table.

For P5 the two selected subfamilies are essential. The entire pair-trace
family need not have intersecting exterior edges, because the partner pair
equal to the unique two-cover defeats the cone choice. Do not apply b≤6 or
the affine bound automatically to that whole family.

## Complete C5/P5 geometry before internal exclusion

For y in a fixed component S let I_y count internal members Q with y∈Q⊆S.
Let G_y count only those whose triple Q\{y} covers the complete C5 star, when
y is C5. Let J_y count internal members containing y and the unique two-cover
C_y of a P5 star, when y is P5. These are counts of actual four-point members;
they must not be replaced by numbers of proper trace labels.

For C5, the strengthened complete-star theorem gives

    d(y)−G_y≤15;
    any non-cover internal member through y forces d(y)≤15;
    d(y)≥16 ⇒ k_y=5+I_y and h_y=s_y=d(y)−5−I_y.

The first inequality follows by deleting all G_y cover-internal triples from
L_y. Sixteen remaining triples would, by the complete-C5 structural theorem,
have an intersecting x-component containing at least six members. Its extras
are internal cycle covers, but these were all deleted. The second and third
claims follow because that theorem puts every internal member in the
x-component and forces it to cover the cycle. The C5 theorem includes the
size-16 R16 and Q8 alternatives explicitly; it is not an unsupported general
claim that every SF3 family of size 16 splits.

For a P5 neighbor, two unconditional/conditional inequalities from the
cover-capacity argument are

    d(y)−I_y+J_y≤16;
    s_y≥8 ⇒ k_y≤6+I_y−J_y.                          (P5)

For the second, B4 makes K_y intersecting. It contains exactly the four
prescribed x-star triples. Every extra avoiding x covers the path. An exterior
extra must contain C_y, so at most 2−J_y such extras are available after
charging the global triple capacity already consumed by J_y internals.
There are at most I_y internal extras. This gives 4+I_y+2−J_y.

For the first inequality, delete the I_y−J_y internal triples not containing
C_y. If seventeen triples remained, choose seventeen including the four
star triples. The universal size-17 decomposition has an intersecting
x-component of size at least seven on support disjoint from the other part.
Every non-star member in it now contains C_y, either because it is a surviving
internal member or because it is an exterior path cover. The pair codegree
capacity two allows at most two extras, leaving size at most six, contradiction.
No arbitrary I7 classification is used.

Under a global cap 18, a P5 neighbor has the following high-degree alternatives
at every central anchor:

| d(y) | possible (s_y,k_y) | internal information |
|---|---|---|
| 17 | (10,7), (9,8), (8,9) | k=7 needs I_y−J_y≥1; k=8,9 has I_y=k−4 |
| 18 | (10,8), (9,9) | I_y=4 or 5 respectively |

The x-component cannot be P10 because x has degree exactly four there, whereas
every used point of P10 has degree five. At size at least eight it also cannot
be Q8, by the point-link shapes described above, so it is P8/P9 on the six
already prescribed points. All its extras are therefore internal. At k=7,
the inequality k≤6+I_y−J_y suffices and does not classify an arbitrary I7.

## Inspection of degree18_component.py before its first scheduled tests

This inspection concerns the constructor's mathematical alterations; it is not
a computation replay or a final review. The original 41 proper component-trace
coordinates retain their multiplicities, with assigned four-point internals
handled separately. The boxes subtract all actual fixed incidences and use
18/6/2 only when the global point cap 18 is an explicit premise.

The root singleton value 18−m, namely eight for P10 or nine for P9, is correct
under the imported disjoint-support complete-link decomposition. The central
anchor's root degree stays 18. Calling local_s_candidates with r10=r9=0 removes
the old singleton bootstrap while retaining the stated universal high-link
and intersecting-signature premises. The μ41 condition is justified by H27 at
|F|≥68, not by the old μ42 result.

The surviving anchor-pair degree-sum bound 19 is also valid: for u,v in an
actual anchor R, members meeting R but avoiding u,v consist of at most two
singleton classes of size ten and one pair class of size three. Thus

    |N[R]|≤d(u)+d(v)−d(u,v)+23,
    d(u)+d(v)≥18+d(u,v)≥19.

This supplies its premise directly without minimum positive degree, sum52,
pair20, or a support cutoff. The sharper codegree-dependent version may be
used where that incidence is represented.

The clean/escape logic is consistent with the stated confinement regimes:
at large singleton s≥8, every internal triple belongs to K. For P-type D its
support is completely exterior; for Q8 D its core is exterior and every D
member contains at least two core points, so no D member can be internal.
At the high-degree regimes, disjoint-support separation gives the same fact.
Hence prescribed star plus all internals must be intersecting in K. For P5,
every exterior escape uses the unique two-cover and the two fresh labels in
the local escape check represent at most two distinct actual extensions.
When k≥8, P8/P9 classification places K on the six prescribed points, so no
such exterior escape is allowed. None of this requires classifying I7.

The new whole-pool lower rows are justified by (EXT) and the equality regimes
above. The strongest additional inexpensive rows identified here are
POOL-affine, the s=9/10 selector pool penalties, and the extra equality regime
s≥8,k≥8. An at-most-one complete-tail state follows from doubled P10 at F≥68.
The full pair/singleton integer table can strengthen branch pruning beyond its
two affine rows, but its nonconvex extra condition should not be imposed as
an unjustified universal linear cut.

## Remaining bridge and source record

No analytic closure of the unrestricted degree-18 branch is claimed. The
terminal separation lemma sharply reduces what is needed at the end: for R99,
excluding four-core and mixed-three-core residuals suffices, with no need to
exclude mixed pairs or pure triples afterward. For P10⊔I8, an at-most-two-core
reduction would suffice. Obtaining those reductions at μ41/r≥50 remains work.

Sources inspected, relative to the frozen Oct20 prior-art68 repository:

- `companion/upstream/D18_P10/PROOF.md`, especially §§1–2,6,8.2;
- `companion/upstream/D18_R99/PROOF.md`, especially §§1,4–5;
- `companion/upstream/D17/UNIVERSAL_EXTENSION_LEMMAS.md`, pair/singleton and
  complete exterior-family arguments;
- `paper/main.tex:206–231,272–331,612–636`, I8/I9/I10, isolation/B4, and
  universal high-link decomposition.

Current Oct23 notes used are `C5-internal-compatibility.md`,
`D19-singleton-I04.md`, `D19-strategy.md`, `doubled-P10.md`, and
`Ysingle-equality-proof.md`. Their structural dependencies remain explicit;
none of the old μ42 finite refutations has been promoted to a size-68 theorem.
