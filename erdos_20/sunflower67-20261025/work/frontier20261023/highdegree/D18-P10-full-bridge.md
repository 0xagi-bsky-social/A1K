# P10 plus I8 at degree eighteen: family-to-model bridge

23 October 2026. Ordinary proof development for the frozen
`degree18_p10_projection_v2.py`, not a final review or a global bound. The
source SHA256 is

    682c441de23f9008fa1cec531a888c12138bbce5ea867a50dd23fb81c5f17cd0

The same hash was checked before and after this inspection. No model was
imported or built, no catalogue was executed, and no solver or Lean command
was run for this note. The only new file written by this task is this note.

**Conclusion.** Every family satisfying the explicit hypotheses below maps
to a feasible point of the frozen model, with residual objective at least
50. No invalid row or local-state rejection was found under those hypotheses.
This is a mathematical bridge to the relaxation, conditional on the named
universal and prior-art inputs. It does not validate a numerical receipt or
assert that every required marked case has been excluded.

## 1. Precise hypothesis and source boundary

Let F be a finite simple four-uniform family with no three distinct members
having equal pairwise intersections; the forbidden common intersection may
be empty. Assume all of the following.

1. `|F| >= 68`, the global maximum point degree is at most 18, and a point x
   has degree exactly 18.
2. The **complete** link of x is the disjoint-support union P10(Y) and I8(Z).
   The universal intersecting classification identifies I8 with P8 or Q8.
   P8 means eight blocks of the displayed canonical P10. Q8 has two hubs,
   a triad, and two leaves, as displayed in the source. Here Y and Z mean
   the full component supports, of sizes six and six or seven.
3. No member of F is a four-set contained in Y. This imports the separate
   new mu41 P10-internal exclusion, recorded in `D18-P10-internals.md` and
   its twelve nonempty-pattern replays. It is not a consequence of the
   current projection or of the old mu42 certificate forest.
4. H27 holds: an intersecting SF4 family has at most 27 members. The
   universal SF2/SF3 capacities, intersecting I8/I9/I10 classification,
   isolation, B4, R16 classification, high-link decompositions, and the
   universal trace margins and compatibility lemmas cited below are
   available.
5. When `crowding_imports=True`, the guarded prior-art cross-star and
   crowding26 results are available. Their precise applicability is
   checked in Section 8. When that switch is false, the ordinary HP16
   result in `D18-pool-research.md` replaces cross15, and no crowding26
   condition is imposed.
6. Each optional branch condition is a true condition on F: the selected
   marker is an actual member; `empty_z` asserts all Z internals absent;
   `assigned_z` gives the **complete** Z-internal pattern; `forbidden`
   excludes every completion of each named exact trace; and
   `forbid_four_core` excludes every residual four-set contained in Y union
   Z. These are additional premises, not deductions made by the options.

The global degree cap is essential. The existence of one degree-18 point
alone does not supply it. None of the arguments below imports minimum used
degree seven, support at most 23, mu42, an old degree-sum threshold, or a
classification of arbitrary intersecting seven-triple families.

Primary frozen sources are under
`work/frontier20261020/prior-art68/repository/`:

| Source | Use in this bridge |
|---|---|
| `paper/main.tex:188–231` | SF2 capacities and canonical/intersecting triple classification. |
| `paper/main.tex:272–376` | Isolation, B4, SF3 bound twenty, exact-trace and codegree bounds. |
| `paper/main.tex:443–462,612–636` | R16 and the universal size-17–20 disjoint-support decompositions. |
| `companion/upstream/MU42/TRACE_FOUNDATIONS.md`, D.1–D.5 | Rooted compatibility, extension-point equalities/distinctions, and five trace margins. |
| `companion/upstream/MU42/scripts/local43.py` | Exhaustive rooted signatures and necessary-state predicates. |
| `paper/main.tex:968–1024` | Arbitrary-support crowding26 and the guarded cross-star theorem. |
| `companion/upstream/D18_P10/PROOF.md:62–97,183–218,289–300` | Pair/singleton resources and whole-component pools, with their universal guards. |
| `companion/upstream/D17/UNIVERSAL_EXTENSION_LEMMAS.md:85–152` | Exterior tail transversals, multiplicities, isolation, and the Q8 leaf caveat. |

The October 23 notes `C5-internal-compatibility.md`,
`D18-structural-tools.md`, `D18-pool-research.md`, and
`PRIOR_DELTA18_UNLOCK.md` give the ordinary deductions and guarded source
transfer used here. In particular the complete-C5 argument at degree 16
checks R16 and Q8 exceptions; no universal split theorem at size 16 is
being assumed.

## 2. Component labels, markers, and arbitrary exterior multiplicities

Write S0 for the eighteen cones `{x} union T`, T in the complete root link,
and R for the members avoiding x. Thus `F = S0 disjoint-union R` and
`|R|=|F|-18 >= 50`.

The source labels Y by 0 through 5, Z by 6 through 11 or 12, and x by 15.
For a mixed-three marker its one actual exterior point is given the next
unused label, 12 or 13. Let C be Y union Z, enlarged by this marked point
when present. All other exterior points remain unrestricted. For every
`U subset C` of size at most four put

    n_U = #{Q in R : Q intersect C = U}.

These are counts of actual members. Proper traces can have arbitrarily
many distinct exterior completions subject to the stated capacities; they
are not Boolean variables. Their sum is exactly |R|. The projected
universe has twelve, thirteen, or fourteen points, but this is not a bound
on the support of F. Four-point traces have no unrecorded completion and
therefore are Boolean by simplicity.

The source's initial upper bounds by trace size are `27,18,6,2,1`. For the
empty trace, every counted member is disjoint from any central cone, so
H27 bounds that class by 27. For nonempty traces, the class is contained
in the corresponding point, pair, or triple star, giving 18,6,2; a
four-set occurs at most once. All initial lower bounds are zero.

The code forces each selected four-member trace to one. A complete
assigned Z pattern forces every other Z-internal four-trace to zero.
Zeroing a proper trace in `forbidden` means absence of **all** its exterior
completions, not just one named member. A clash with a selected member is
reported as a conflict, so it cannot silently change the branch premise.

### Completeness of component and marker coverage

`automorphisms` ranges through every permutation of the full used support
and tests equality of the block family. Thus it returns the full component
automorphism group. `p8_deletion_types` starts with all 45 pairs of removed
P10 blocks, removes each complete orbit, checks disjointness and coverage,
and requires exactly the two types indexed by omitted-block intersection
size one or two. Conditional on that constructor returning successfully,
no P8 deletion type is omitted. There is no guessed stabilizer assumption.

For each I8 type the marker catalogue partitions three domains under the
product of these full component groups, fixing the marked exterior point:

* every Z-internal four-set;
* every four-set on Y union Z meeting both components;
* every mixed three-set on Y union Z with the one exterior point appended.

These are precisely all four-core members except the fifteen already
excluded Y internals, and all mixed-three-core residual members. Each
orbit is generated from every product-group element; the code checks
disjointness of successive orbits and equality of their union to the
declared domain. The raw domain sizes follow from binomial counts: 480
four-core plus 180 mixed-three markers for P8, and 700 plus 231 for Q8.
This note has not run those checks or asserted numerical orbit totals.

Any actual member of one of these types can be brought to the corresponding
representative by an actual component automorphism and, for a mixed triple,
renaming its sole exterior point. Further branch restrictions must be
transported under the same relabeling: a representative case does not
automatically preserve a separately fixed noninvariant forbidden pattern.

### Fixed-member sunflower tests

All members in `fixed` are actual members lying in `C union {x}`: the
eighteen cones and the selected residuals. The source rejects a sunflower
among them. For two fixed members A,B, it also sets `n_U=0` when

    U intersect A = U intersect B = A intersect B.

For any completion Q of U, these are exactly the three pairwise
intersections of Q,A,B. If Q equals one of the two fixed members, equality
would force two distinct four-sets to contain one another; hence the test
never falsely uses repeated members. Pairs of two cones are omitted from
this test because their intersection contains x while Q avoids x; they
could never satisfy it. No test compares two unmarked proper traces as
though their unrepresented exterior intersections were known.

## 3. Every global incidence and actual-anchor row

For a nonempty represented set U of size one, two, or three, let
`b(U)=#{B in S0 : U subset B}`. The implemented incidence inequality is

    sum_{V containing U} n_V <= cap(|U|)-b(U),
    cap(1)=18, cap(2)=6, cap(3)=2.

All occurrences through the distinguished root are already in S0. The
marked exterior point has zero fixed incidence. Selected residuals remain
among the n variables; they are never subtracted twice.

For each actual anchor A in `fixed`, the following rows hold.

**Disjoint H27.** The members of F disjoint from A form an intersecting
family: two disjoint ones together with A would be an empty-core sunflower.
Thus

    sum_{V disjoint from A} n_V <= 27-#{B in S0 : B disjoint from A}.

**Actual-anchor mu41.** The same fact and `|F|>=68` give `|N_F[A]|>=41`.
The row is precisely

    -sum_{V meeting A} n_V <= #{B in S0 : B meets A}-41.

Both assertions count actual intersections because A is wholly represented.
This remains true for a mixed-three marker: its exterior point is retained
as a coordinate. A mu41 row at an unselected arbitrary four-set would not
be justified, but the source imposes it only at actual anchors.

**Exact-trace caps.** For every nonempty proper U subset A, the members
whose exact intersection with A is U have distinct, intersecting,
sunflower-free residues after U is removed. Two disjoint residues with A
would give a sunflower with core U. The intersecting bounds are 10,3,1
for residual ranks three,two,one. Hence

    sum_{V : V intersect A = U} n_V
      <= cap_exact(|U|)-#{B in S0 : B intersect A = U},
    cap_exact(1)=10, cap_exact(2)=3, cap_exact(3)=1.

**Pair degree nineteen.** For u,v in A, the neighborhood members avoiding
both have exact trace one of the two remaining singletons or their pair.
There are at most `10+10+3=23`. Therefore

    41 <= |N_F[A]| <= d(u)+d(v)-d(u,v)+23,
    d(u)+d(v) >= 18+d(u,v) >= 19.

The last inequality uses the actual member A containing the pair. The
source subtracts the two fixed-star degrees and puts the negative residual
incidence sum on the left. If u=x, its residual contribution is zero and
its full degree 18 is already in the fixed term. This does not impose a
degree-sum lower bound on pairs not known to occur in an actual member.

**Crowding26.** With the import enabled, for each three-element subset of
the four points of A, the sum of its three exact singleton counts is at
most 26. The source subtracts their known cone contributions. These four
inequalities are equivalent to the bound on the three largest counts;
the guards and arbitrary-support dependency are checked in Section 8.

The objective is `sum n_U`. There is no residual lower row in the
optimization model. Nevertheless the mapped hypothetical F has objective
at least 50. Its use of mu41 and the other size-68 deductions remains
valid; allowing other model points of smaller objective does not require
those points to correspond to smaller actual families.

## 4. Universal completeness of the central local domain

Fix a cone `A={x,a,b,c}` with `a<b<c`. Its six exact pair counts p are
ordered `xa,xb,xc,ab,ac,bc`; t_i is the exact triple count omitting the
ith point of `(x,a,b,c)`, and s_i is its exact singleton count. For the
complete link of the ith point let D_i be disjoint from the link anchor
`A minus {i}` and K_i its closed neighborhood. Then

    |D_i|=s_i,
    |K_i|=k_i=1+sum_{j not i} p_ij+sum_j t_j-t_i,
    d(i)=s_i+k_i.

The complete root link fixes `p_xa,p_xb,p_xc,t_a,t_b,t_c,s_x` by actual
intersections with the eighteen cones. The other seven coordinates are

    (p_ab,p_ac,p_bc,t_x,s_a,s_b,s_c).

They are exactly the source's seven trace-bucket sums: the three pair
subsets of T, T itself, and its three singleton subsets. Since the
residuals avoid x, their exact trace on A is their exact trace on T.
Cones contribute to none of these seven non-x classes.

The loop ranges over all `p_ab,p_ac,p_bc in {0,1,2,3}`, `t_x in {0,1}`,
and all singleton candidates in 0 through 10. It imposes the following
necessary tests, and no ordering of actual point degrees.

1. `local_s_candidates(i,p,t,17,0,0)` uses the universal range 1 through
   20, while the caller enforces degree at most 18. Its zero bootstrap
   parameters add no old lower bound to k at singleton size nine or ten.
2. At degree 17 the high-link theorem permits `(s,k)=(7,10),(8,9),(9,8),
   (10,7)`; at degree 18 it permits `(8,10),(9,9),(10,8)`. A link anchor
   lies in one of two intersecting parts on disjoint supports, so its
   neighborhood is exactly that part. This is valid for an arbitrary I7.
3. If s is at least eight, B4 makes K intersecting and gives k at most
   ten. The D6 resource argument gives `sum p_ij<=6`. D8 gives `p_ij<=2`
   when the complementary occupied triple class forces its extension
   point into every edge of that pair class. At k at least nine, D7 bounds
   each p_ij by two from the P9/P10 rooted model.
4. The helper's `SIG[k]` for k=8,9,10 is built from **every** k-subset of
   the ten canonical P10 blocks, plus Q8 at eight, every member serving
   as anchor, and every ordering of that member. Its three exact
   singleton and complementary-pair counts are the actual `(alpha,tau)`.
   Under the intersecting classification, this necessarily includes each
   actual rooted signature. It does not classify k=7.
5. `1+sum p+sum t+sum s>=41` is the actual-anchor neighborhood bound.
   The six pair-degree tests follow from Section 3. The five-margin
   threshold `(12,14,17,19,22)[#{i:s_i<8}]` is precisely the universal
   D.3–D.5 theorem.
6. For occupied triple classes write their actual exterior points z_i.
   D9 forces `z_i=z_j` when both indices are large, their triple classes
   are occupied, and p_ij=2. The union-find test takes the transitive
   closure of these equalities. At a large index with k at least nine,
   its P9/P10 model requires the other occupied z_j to be distinct.
   Rejecting a conflict is necessary; the test need not detect all
   other obstructions. It does not equate points merely because two
   counts agree.
7. When enabled, the three-largest-singleton test is crowding26 at this
   actual cone. The remaining geometric, cost, and pool tests are
   justified below.

### The root and the opposite I8

The root's own helper call is sound and matters in the Q8 branch. For T
in P10(Y), the root has `(s_x,k_x)=(8,10)`, with its actual I8 disjoint
family outside Y and its near family P10. For T in I8(Z), it has
`(s_x,k_x)=(10,8)`: the near family is the actual I8, including Q8 when
present. The exact px and tf counts are obtained from this I8, not copied
from P10. Q8's rooted signatures are explicitly in SIG[8]. This call does
not require the opposite eight-member family to have six-point support,
nor impose a C5/P5 star or an exterior-singleton equality on Q8 vertices.

### New complete point-link graph filter

At a neighbor v in T, the link anchor in L_v contains x. Thus **every**
triple of L_v containing x belongs to K_v, and its full point-link at x
is exactly

    {B minus {v} : B in L_x and v in B}.

Completeness of L_x is the reason there are no additional edges. If
`s_v>=8` or `d(v)>=17`, B4 or the high-link theorem makes K_v intersecting.
If additionally `k_v in {8,9,10}`, the universal classification applies.

`intersecting_point_link_templates(k)` records the complete graph at every
used point of every canonical k-subfamily, including Q8 at k=8. The graph
signature discards isolated vertices of the graph and minimizes over all
permutations of its used vertices. Isomorphic graphs have equal signatures;
all actual classified roots occur among these templates. Hence a mismatch
is a valid rejection. This uses no equality between K_v's whole support
and the support of its point-link graph. Such equality is invoked only
later, with a separate six-point argument. The filter has no k=7 branch.

In particular the hub graph of Q8 is a triangle together with a two-edge
path on disjoint graph vertices; its triad graph is C4 and its leaf graph
is a single edge. The hub graph is not C5. A Q8 near family of size eight
can coexist with an opposite P10 at total degree 18; the source does not
exclude this merely because its graph differs from a cycle.

## 5. Literal C5 and P5 rows with their actual resources

For a represented core point v let W be its component Y or Z. The literal
shape test first requires `|W|=6` and that the complete graph at x in L_v
uses **all five** points of `W minus {v}`. It then verifies connectedness
and the full degree sequence for C5 or a four-edge path on five vertices.
Consequently the five cycle/path vertices together with x are six actual
points already in the support of every near family containing this star.
Q8 has seven-point component support and receives none of these cuts.

Define actual integer resources

    I_v = #{Q in F : v in Q subset W},
    G_v = #{Q counted by I_v : Q minus {v} covers the C5},
    J_v = #{Q counted by I_v : Q contains the unique P5 two-cover C_v}.

Their implementations sum distinct four-point trace variables. The
`removable` resource is exactly `I_v-J_v`, not the full internal count.

### C5: why d(v)-G_v <= 15

Remove from L_v all G_v cycle-cover internal triples. Its complete x-star
is still precisely C5. If at least sixteen triples remain, the complete-C5
lemma supplies two intersecting components on disjoint supports. The
x-component contains the five prescribed star triples and, since the
opposite component has at most ten, at least one extra triple. An extra
must cover C5 and therefore uses three of its five vertices; it is an
internal cycle cover, although all such triples were removed. This
contradiction gives `d(v)-G_v<=15`.

For clarity, the complete-C5 lemma's size-16 proof first excludes R16,
whose used point degrees are four or six, not five. B4 then gives two
intersecting parts. A P-type part has disjoint support from the other by
isolation. If both parts are Q8, x can be a core point in neither because
a Q8 core point-link has a triangle or C4, impossible as a subgraph of
C5; shared leaves give total degree at most two. Thus that exception is
also excluded. The size-17–20 cases use the universal high-link theorem.

Whenever `s_v>=8` or `d(v)>=16`, K_v is intersecting in the needed form.
Every triple in it avoiding x covers the five-cycle and is a G_v triple.
Hence `k_v<=5+G_v`. Both inequalities justify the source cost

    G_v >= max(0, d(v)-15,
                   k_v-5 if s_v>=8 or d(v)>=16 else 0).

The global row removes exactly the G_v columns from residual point
incidence and subtracts the five fixed cones, so it is exactly
`d(v)-G_v<=15`. On Y, I_v=G_v=0 by the explicit internal-empty premise.
Thus `d(v)<=15`, and at s_v at least eight also k_v at most five. These
are precisely the additional Y state rejections and degree-selector cap.

### P5: removable capacity and the unconditional bound

A path on five vertices has exactly one two-vertex cover C_v. An extra
triple of an intersecting near family, avoiding x, must cover the path.
If it is not wholly on the five prescribed vertices, it must contain
this two-cover and one exterior point. In L_v, the pair C_v has codegree
at most two. Its J_v internal occurrences consume that same capacity.

When K_v is intersecting in the source's regimes `s_v>=8` or `d(v)>=17`,
there are four star triples, at most I_v internal extras, and at most
`2-J_v` exterior extras. Every J_v triple meets every star anchor because
C_v meets every path edge, so subtracting J_v charges occurrences in the
same resource. It follows that

    k_v <= 6+I_v-J_v.

For the unconditional statement, delete the `I_v-J_v` internal triples
which do not contain C_v. The four star triples remain. If seventeen
triples remain, a size-17 subfamily containing those four stars has a
disjoint-support intersecting decomposition, with x-component of size
at least seven. All its extras avoid x and cover the path. A surviving
internal extra contains C_v by construction; an exterior extra contains
C_v by the unique two-cover property. There are at most two such extras,
so the x-component has at most six, a contradiction. Therefore

    d(v)-I_v+J_v <= 16.

The global source row removes only `removable=I_v-J_v` from point
incidence and subtracts the four fixed cones. The conditional selector
cost is exactly

    I_v-J_v >= max(0, d(v)-16,
                       k_v-6 if s_v>=8 or d(v)>=17 else 0).

No part of this argument classifies a seven-member intersecting family.

### P5 high states and the k-4 internal charge

At degrees 17 and 18, the universal disjoint-support split makes K_v
intersecting. Its complete point-link at x has four edges, so K_v cannot
be P10, where every used point has degree five. This leaves exactly

    d=17: (s,k)=(10,7),(9,8),(8,9);
    d=18: (s,k)=(10,8),(9,9).

If `s>=8` and `k>=8`, B4 also makes K intersecting. Its complete P5
point-link excludes Q8 (none of Q8's three rooted graph shapes is P5).
Hence K is a P8 or P9, with six-point support. That support already
contains all six prescribed points `{x} union (W minus {v})`; the two
supports are therefore equal. Its k-4 non-x triples are distinct actual
internal triples. In particular

    I_v >= k_v-4   when s_v>=8 and k_v>=8.

The lower bound alone does not need every internal member to lie in K.
At high degree, disjoint-support separation gives that stronger fact as
well. Degree 17 needs at least one removable internal by the unconditional
bound, and therefore at least one internal. Degree 18 has k=8 or9 on the
six prescribed points and needs at least four internals. Thus the source
cost

    I_v >= max({17:1,18:4}.get(d(v),0),
               k_v-4 if s_v>=8 and k_v>=8 else 0)

is necessary. The k=7 state is handled only by the cover capacity and
degree-deletion argument. No I7 catalogue or support bound is inserted.

## 6. Whole-component singleton lower bounds, including Q8 leaves

For a literal C5/P5 point v in six-point W define H_v to be the complete
family of tails H outside `{x} union W` with `{v} union H in F`, and
write h_v=|H_v|. It is exactly the global sum of n_U with
`U intersect W={v}`, including all marked and unmarked exterior
completions. At a central anchor through v, always `H_v subset D_v`, so
h_v<=s_v. The lower bounds used by the source are

    h_v >= ell(s_v),
    ell(8)=6, ell(9)=9, ell(10)=10, ell(s<=7)=0.

D_v is intersecting SF3. If it is P8, P9, or P10, its support avoids the
link anchor. Isolation says a K_v triple meeting that support would be a
deleted P10 block; that block also avoids the anchor and would belong to
D_v instead. Hence K_v avoids the entire support of D_v. The prescribed
complete star in K_v spans all six points `{x} union (W minus {v})`.
Therefore all D_v tails avoid them, and h_v=s_v.

For D_v=Q8 at s_v=8, only its five-point core is isolated. Both possible
exceptional hub-plus-two-leaf triples avoid the link anchor, since every
Q8 point occurs in D_v and avoids that anchor. They cannot lie in K_v.
Thus K_v avoids the Q8 core, putting that core outside the six prescribed
points. Its six core-only triples are exterior tails, so h_v>=6. The two
leaf triples may touch W at their leaves; h_v=8 is not assumed.

The source replaces ell by the full s_v in exactly these additional
regimes:

* C5 and `d(v)>=16`: the complete-C5 theorem gives its x-component on
  the prescribed six points and the opposite component exterior.
* P5 and `d(v)>=17`: the high-link split has disjoint supports. The
  x-component contains all six prescribed points, so the opposite
  component is exterior; any extra in the x-component covers the path
  and cannot be an exterior singleton tail.
* either literal shape with `s_v>=8,k_v>=8`: K_v is intersecting and
  its complete point-link excludes Q8. Its P-type support consists of
  exactly the six prescribed points. By isolation, a D_v triple meeting
  this support would be a deleted P10 block; every such block meets the
  actual P-type anchor, contradicting its membership in D_v. Thus the
  whole D_v is exterior.

In all three cases D_v=H_v. The source has no equality or `h>=s-2`
rule for `s<=7,k>=8` alone. It also adds no whole-component lower bound
at a seven-point Q8 vertex. These two restrictions are essential.

For each local selector distribution the source enforces
`h_v >= sum_r lambda_r lower(r,v)`. An actual family chooses its one
actual state, where the inequality has just been proved. Using the same
h_v at every anchor is legitimate because it is one actual global tail
family, not an independent copy attached to each anchor.

## 7. Every shared P10 pool row

Only Y receives these pool rows. Put `P=sum_{y in Y} h_y`, and let b_y
count all residual members whose exact Y trace is a pair containing y.
Cones have Y trace either empty or a triple, so they contribute to
neither statistic and no fixed contribution is subtracted here.

Two singleton-pool members with the same centre share it. If two with
different centres y,z were disjoint, a P10 block avoiding y,z exists:
P10 has exactly `10-5-5+2=2` such blocks. Its cone is disjoint from
both, giving an empty-core sunflower. Therefore their union is
intersecting SF4, and H27 yields P<=27. Each H_y is intersecting SF3:
two disjoint tails together with a fixed cone through y give a
sunflower with core y. Consequently h_y<=10.

The same avoided-block argument makes distinct H_y,H_z cross-intersecting.
Any one tail belongs to at most two of them by triple codegree two.
If h_y=10, its P10 has no two-cover and exactly its own blocks as
three-transversals. Every other tail belongs to those ten blocks, so
P<=20. If h_y=9, its P9 has no two-cover and eleven three-transversals,
giving P<=22. Exterior points in a triple transversal would leave at
most two support points and are impossible. Thus the source's affine
and conditional rows are valid:

    2P+7h_y <= 110;
    P+5*[s_y=9]+7*[s_y=10] <= 27 at each central anchor through y.

For the affine row, h_y<=8 gives at most54+56=110; h_y=9 gives at most
44+63=107; h_y=10 gives at most40+70=110. The conditional row uses
h_y=s_y at singleton sizes nine and ten from Section 6. Penalties are
used separately at each point/anchor; the code does not add penalties
for unrelated points into one unjustified inequality.

### Pair/singleton affine resource

Write a pair-pool member through y as `{y,j} union E`, with exterior
two-set E. At the C5 point y, these E are pairwise intersecting. For
different partner points j,k a cycle edge avoids both, since C5 has
no two-cover; for equal partners use a cycle edge through that partner.
Disjoint E's would give a sunflower with a prescribed cone, of core y
or `{y,j}` respectively. Each singleton tail H in H_y meets every E:
a cycle edge avoiding j supplies the forbidden sunflower otherwise.
Each E has multiplicity at most two by codegree two of `{y} union E`.

An intersecting simple graph is a star or triangle. A star's centre
uses pair-codegree capacity six with y, giving b_y<=6. A triangle has
three edges of multiplicity at most two, also giving b_y<=6, and its
three triple resources give `b_y+h_y<=6`. For a star with two or more
leaves, at most two singleton tails omit the centre and at most
`6-b_y` contain it, so `h_y<=8-b_y`. At b_y>=5 there are at least three
leaves, leaving at most one tail omitting the centre, and
`h_y<=7-b_y`. With a single edge, `b_y<=2` and the two endpoint
pair-codegrees give `h_y+2b_y<=12`. Together with h_y<=10 this yields

| b_y | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---:|---:|---:|---:|---:|---:|---:|
| h_y at most | 10 | 10 | 8 | 5 | 4 | 2 | 1 |

Substitution at these seven integers gives the implemented consequences
`b_y<=6` and `5h_y+9b_y<=59`. The source uses only the C5 Y side for this
whole-pair-pool row. It does not apply the argument to the entire pair
pool of a P5 vertex, where its unique two-cover would invalidate the
avoided-edge step, or to an arbitrary I8 component.

## 8. Cross15, crowding26, and their exact guards

`PRIOR_DELTA18_UNLOCK.md` identifies the prior results newly applicable
under the explicit global cap18. In the frozen paper's crowding proof,
the cross-star theorem assumes two distinct centres a,b outside **both**
tail supports, intersecting SF3 tail families, cross-intersection between
them, and all their four-set lifts lying in the same SF4 family. If their
total is at least sixteen, it supplies an actual anchor with

    |N[A]| <= d(a)+d(b)-d(a,b)+4 <= 40.

For H_y,H_z, both centres are in Y and every tail avoids Y and x. The
intersection, cross-intersection, and actual-lift guards were proved in
Section 7. Mu41 from Section 3 therefore gives `h_y+h_z<=15`, exactly
the fifteen `Y-imported-cross15` rows. This does not require the Y
internals to be empty. When imports are disabled, the weaker HP16
argument in `D18-pool-research.md` uses the same actual-tail guards
plus `|F|>=68,Delta<=18`, and supplies the source's fallback 16.

The pruning of a Y local state whose two certified lower bounds sum
above 15 (or16) is also necessary: both lower bounds apply to the same
actual global pool sizes. It is not a comparison between independently
invented families.

Crowding26 says that at every actual anchor the three largest exact
singleton counts sum to at most 26, under `mu>=41,Delta<=18`. Its
singleton tails avoid the entire anchor; the finite reduction retains
all fresh support identifications, including Q8 leaves. The written
reduction extracts the violating colour-size patterns `(10,10,7)`,
`(10,9,8)`, or `(9,9,9)`, then uses normalized support positions,
literal rainbow intersections, and capacity certificates or guarded
cross-stars to find a neighborhood at most40. The source applies this
result only to actual central or selected anchors, and to their actual
singleton counts. No global support bound is used in that application.

These two results are imported with finite certificate dependencies;
this note does not replace those dependencies by a claim of a purely
analytic proof. The frozen dependency record contains

* `companion/terminal/cross15/results/cross16_certificate.json` and
  `companion/terminal/cross15/src/verify.py`;
* `companion/terminal/crowding/certificates/crowding26.json.gz` and
  `companion/terminal/crowding/code/verify.py`;
* the prior `FOUNDATION_LEDGER.md` and
  `replay-selected-20261020/RECEIPT.json`;
* the current `prior-delta18-unlock.json` matching the frozen package
  and four saved checker outputs to those earlier replays.

The constructor hashes these dependencies when the imports are enabled.
The October20 normal and optimized runs are reused, not rerun here;
running one checker in two interpreter modes is not independent
mathematical verification. The separate prior conclusions about minimum
used degree and support size are not among the rows or prerequisites of
this projection.

## 9. Pruning, degree distributions, and the actual integral witness

For each central anchor, choose the local row consisting of its seven
actual statistics. Sections 4–8 show it survives every semantic filter.
It also survives the purely numerical pruning:

* each bucket total lies between the sums of its coordinate lower and
  upper bounds;
* each required internal, removable, or cover resource is at most its
  actual resource, hence at most the sum of those upper bounds;
* the actual degree is at least its fixed-cone contribution plus the
  forced selected incidences, and at most18 (at most15 on Y).

Give the selector for that actual row weight one, and every other row
weight zero. Duplicate metadata rows, if present, cause no problem:
choose any occurrence of the actual row. The normalization and all seven
bucket equalities hold. The three resource inequalities, whole-component
singleton lower row, and conditional Y-pool row hold by the preceding
proofs. Multiple anchors use the same actual global resources; the code
does not sum their individual lower requirements as independent costs.

With `degree_distributions=False`, no degree selectors are present;
the seven bucket equalities already make each local degree equal the
same global incidence sum at a represented point. When the option is
true, choose weight one on the actual degree at each point. The global
incidence equality and every local degree-distribution equality then
hold. The listed degree range starts only at the forced fixed incidences,
not at a universal positive minimum. A marked exterior point is included
in these choices and incidences, but needs no central local catalogue.

Thus the actual trace vector, together with these zero-one selectors,
satisfies every box, upper row, and equality returned by `build`. All
unknown exterior labels have been used only to define exact counts or
to prove universal geometric implications; none has been artificially
identified or confined to a finite exterior universe.

## 10. Consequence for exact arithmetic and remaining obligations

Write all columns as z with finite integer boxes `[l_j,u_j]`, upper rows
`Az<=b`, equalities `Ez=f`, and c equal to one on trace columns and zero
on selector columns. For nonnegative integer upper-row weights y,
signed integer equality weights e, and positive integer scale D, put

    q = A^T y + E^T e,
    H = b^T y + f^T e,
    B = H + sum_j max(l_j*(D*c_j-q_j), u_j*(D*c_j-q_j)).

Then `D*c^T z <= B` for every feasible point. This is exactly the
integer-box diagnostic in the source. All source matrix coefficients
and right sides are small integers; conversion to floating sparse
storage does not change their values. Rounded solver marginals merely
propose y,e; the exact recomputation and the finite-box correction, with
all selector columns retained, establish the inequality. A separately
replayed `B<50D` excludes the stated case. Equality at50 needs another
argument. A numerical infeasibility status alone is not an exact proof.

An exact replay must bind this frozen source, local43, the imported
dependencies, the kind, selected marker and complete literal branch
premises, every box, and the rebuilt row order. This note supplies the
family-to-model direction independently of any particular solver output.
It neither replays a certificate nor establishes a complete list of
excluded cases.

Once all four-core and mixed-three-core cases have actually been
excluded, the separate asymmetric terminal lemma in
`D18-pool-research.md` Section 8 bounds the remaining residual family by
37. That terminal restriction is not assumed anywhere in this model.
Closing all marked cases, transporting any extra branch premises, and
combining their exact bounds with that terminal argument remain separate
proof obligations.

### Inspection hashes

The frozen constructor hash above was equal before and after inspection.
The other source bytes read for this bridge had the following SHA256
values; these identify this inspection, not a new replay of their proofs.

| File | SHA256 |
|---|---|
| `local43.py` | `258221ffe8594e51616bdd125109d92151bfea13557f4e385ef453ab2e03152b` |
| frozen `paper/main.tex` | `4aa36c9d56af5a8e3bdb44749107820549a73e0d3405e6c700104fa4c30e5c21` |
| `D18-structural-tools.md` | `3ca78644de3e4aaab94372300b9b3f3801ae79ba73766d2784d39d741302fc33` |
| `D18-pool-research.md` | `7a5422df629f7f9e5137be88b9d7fdf52ccf39f309fd1fdc49a728dea24803a8` |
| `PRIOR_DELTA18_UNLOCK.md` | `25b65f695264ae0dbcd5d97b8e66eac421cccbb9970eaf20cc8692886f855b89` |
| `prior-delta18-unlock.json` | `574774b2a12665f403932dcd45fe8269c84d105d60db367e357f27fa8c10442f` |

Assurance: source-inspected ordinary family-to-model proof, conditional on
the explicitly imported structural theorems, H27, the prior cross15 and
crowding26 dependency chain when enabled, and the literal case hypotheses.
No whole-degree18, end-to-end Lean, or global size-67 claim is made.
