# Degree17 full projection: ordinary family-to-model bridge

23 October 2026. This is ordinary proof development, not final review,
Lean verification, or a claim that degree17 or the global size67 problem
is closed. No model import, catalogue generation, model build, solver,
certificate replay, or new finite census was run for this inspection.

The inspected original is `degree17_full_projection.py`, SHA256

    3d79ea4a0755f59aa8107c89d773600bc0965aa751772c337c3431c3a7caff52.

The hash was checked before inspection and again after preparing the
separate v2 source. No bad mathematical row was found under the explicit
imports below. The family map and its guards are given here so that a
later exact arithmetic certificate has a precise mathematical target.
The additional generic two-actual-anchor rows in the separate v2 source
are justified in Section 12; the original remains frozen.

## 1. Conditional hypotheses and source boundary

Let F be a finite simple four-uniform family on an arbitrary ground set,
with no three distinct members having equal pairwise intersections;
the prohibition includes the empty core. Suppose

    |F| >= 68,       d_F(x)=17,       max_v d_F(v) <= 17.

The maximum-degree assumption is supplied explicitly. It does not depend
on the current status of any degree18 computation. Exactly seventeen
members contain x; hence the residual family F minus those cones has
size at least51. The target51 is a lower bound on the actual objective,
not an equality imposed by the projection.

The following prior universal results are imported: H27 for intersecting
SF4 families; the SF2/SF3 incidence and exact-anchor capacities; isolation,
B4, R16 and the high-link decomposition; the intersecting I8/I9/I10
classification; the universal necessary local trace restrictions encoded
by `local43`; and the prior mu41/cap18 crowding26, guarded cross15 and
minimum-used-degree7 results. The I7 classification has the separate
arbitrary-support and finite-coverage justification in Section 2.

The frozen mathematical sources are under
`../../frontier20261020/prior-art68/`, principally:

* `repository/paper/main.tex:188–231,272–376`: small-uniformity capacities,
  isolation, B4 and the SF3 bound20;
* `repository/paper/main.tex:443–514,612–636`: R16, I7 support reduction
  and complete size17 link alternatives;
* `repository/companion/upstream/MU42/TRACE_FOUNDATIONS.md`, D.1–D.5,
  together with `scripts/local43.py`: universal necessary local states;
* `repository/paper/main.tex:968–1024`: crowding and guarded cross-star
  results with their arbitrary-support reductions;
* `analysis/mu41/mu41-analysis.md`, Section 3: minimum used degree7;
* `FOUNDATION_LEDGER.md` and the saved selected replay receipt: prior
  execution provenance, not a new replay by this inspection.

The local structural bridges are `D18-structural-tools.md`,
`D18-pool-research.md`, `D18-additional-core-rows.md`,
`D18-Q8-internal-research.md`, `C5-internal-compatibility.md` and
`D19-singleton-I04.md`. The repeated C5/P5 and pool arguments are also
expanded in `D18-P10-full-bridge.md`; Section 8 below states their exact
degree17 use. Prior crowding imports and their guards are described in
`PRIOR_DELTA18_UNLOCK.md`. These are imported ordinary theorems and
selected finite verification records, not kernel-checked proofs here.

The producer hashes its source, local43, structural and pool notes, and
the files in `CROWDING_SOURCES`, including the I7 package and its independent
coverage receipt. Merely hashing a theorem source does not prove it.
The claimed implication is conditional on these stated mathematical
inputs and the supplied branch premises.

## 2. Why the eleven root forms cover arbitrary support

The complete degree17 link splits on disjoint supports as P10 plus an
intersecting I7, or P9 plus an intersecting I8. The P9 is P10 with one
block deleted. The I8 alternatives are P10 with two blocks deleted,
whose two deletion orbits are distinguished by intersection size1 or2,
and Q8. Thus the three latter forms are `P9-P8-i1`, `P9-P8-i2`, `P9-Q8`.

For I7 the ordinary support reduction is needed independently of any
six-point enumeration. Here is the reduction checked against
`D17-I7-classification-route.md` and the frozen paper. In an intersecting
SF3 family of seven triples, no point can have degree6: its complete
SF2 link would be two disjoint triangles, requiring a four-point cover
for the remaining triple. Degree5 has complete link C5 or a triangle
disjoint from a two-edge path. C5 forces all three points of each
noncentral triple onto its five-point support, giving six support
points. In the other case every three-cover uses two triangle vertices
and the path middle, and the two additional triples give the unique
seven-point H7, a Q8 with one core-only triple removed.

With maximum degree at most4, a degree-one triple luv splits the other
six triples into u-only, v-only and uv classes of sizes (3,3,0) or
(3,2,1), up to exchanging u,v. The three-edge residual family is a
triangle; cross-intersection forces the other residual edges onto that
triad. The first case has six support points. The second is H7 (and
therefore actually has a degree5 hub). If no point has degree1, let
b,c,d count degrees2,3,4 and B count codegree-two pairs. Then

    2b+3c+4d=21,       B=b+3c+6d-21,       2B>=c+2d.

The last inequality follows from the SF2 links of sizes2,3,4 having
at least0,1,2 degree-two vertices. It implies 2d>=2b+c. Writing
21=3(b+c+d)-b+d gives support size at most7. Equality would force
b=d,c=0, making the support even, so it is at most6. Support at most5
is impossible since the21 pair incidences exceed ten pairs of cap2.
Consequently the six-point cases and H7 exhaust arbitrary supports.

The finite six-point part is separately covered by
`D17_i7_coverage.py`. Its saved receipt reports all77520 seven-subsets
of the twenty triples inspected by literal intersection tests, exactly
1860 valid labelled families, and disjoint full-S6 template orbits of
sizes120,360,60,240,360,360,360 with precisely that union. It checks
the seven-point H7 separately. The full projection does not use its
additional175 mixed-trace classification entries.

The seven-certificate SHA256 is

    fe172301b201819c029d9a1b7e8931f516cbd90aa978977118b7853b2ead7164.

The independent checker and saved receipt hashes read here are

    checker fa59a11857d7dfdc3047a660f6fcb6204206ac311880e95e1f52c373718909a9
    receipt 030fcb5ec6e64c738f306409fca83ed962c3afefb5225378295d3a6601c196df.

The loader checks the pinned certificate, receipt/source identity,
counts, and IDs0 through7; it does not rerun the census. The receipt is
evidence for that finite domain, while the preceding argument supplies
the arbitrary-support reduction. The templates are therefore the eight
`P10-H0` through `P10-H7` forms, without importing an R16-specific outer
hypothesis. H0 through H6 use six points; H7 uses seven.

## 3. P10 empty internals and the exact68 dependency

The P10 forms impose absence of all fifteen four-sets within Y. This is
an explicit dependency on the separate degree17 component exclusion
of P10_001 through P10_012. It is not justified by any degree18 receipt.
`D17-P10-internals.md` gives that component model's ordinary bridge;
`replay_component17.py` is the separate arithmetic reconstruction tool.
The full producer checks and records the twelve existing receipt hashes
and their reported negative gaps, while expressly not replaying them.
A complete use of the exclusion requires the separately checked exact
certificates, not just the producer's metadata test.

There is a cardinality guard worth making explicit. The component
model's residual budget uses exactly68 members. Suppose a family F
as in Section 1 has a nonempty P10 internal family I. Retain all17
root cones and every member of I, of which there are at most15. This
fixes at most32 members. Extend this collection to a68-member subfamily
F'. It remains SF4 with cap17; its root degree is still17 and its complete
root link is unchanged. Its entire Y-internal family is exactly I,
because every such member of F was retained. Thus the exact68 component
exclusion rules out the same nonempty pattern in F. This proves the
required hereditary transfer to |F|>=68 without applying the component
budget directly to a larger family.

In all three P9 forms the source sets `empty_y=False`. All fifteen Y
internals remain free, including when a single `IY` marker is prescribed.
There is no transfer of P10 emptiness to P9. Opposite Z internals are
free in every form except explicit `empty_z` or complete `assigned_z`
branch assumptions.

## 4. Actual coordinates, exterior multiplicities and markers

Relabel x by15, Y by0 through5, and Z by6 through11 or12. Let C be
Y union Z, with an additional represented exterior point if the chosen
marker contains one. Its label is the next unused core index, at most13,
so it is distinct from x. No other exterior points are represented.
For every U subset C of size at most4 define

    n_U = #{Q in F : x notin Q and Q intersect C = U}.

These nonnegative integers count arbitrary multiplicities of distinct
actual completions on the unrepresented exterior. They partition the
entire residual family, including empty traces. In particular

    sum_U n_U = |F|-17 >= 51.

The finite coordinate universe is a projection, not an ambient support
bound. A four-point trace is the actual four-set U, hence has binary
membership. A proper trace may have many different exterior completions.

The full automorphism group of each displayed component is obtained
by checking every S6 or S7 permutation. Their product acts independently
on Y and Z and fixes the represented exterior point. The marker domains
are all permitted Y internals (`IY`, P9 only), all Z internals (`IZ`),
all mixed four-core sets (`E4_`), and all mixed three-core sets together
with one actual exterior point (`E3_`). The orbit loop checks disjointness
and exact union with each domain and the total requested domain.
Any actual marked set can be carried to its representative by relabeling
the whole family, with an arbitrary bijective relabeling of its actual
exterior point. This does not assume the family is symmetric.

Branch restrictions must be carried by the same relabeling: a complete
assigned Z pattern specifies presence and absence of all Z internals;
`forbidden` sets the entire exact-trace class to zero, including every
exterior completion; `forbid_four_core` excludes every actual four-set
inside the original core. The unmarked case adds none of these premises.

Let S_x be the seventeen fixed root cones and let B be S_x together
with the selected marker and assigned present Z internals. Every member
of B is actual. Selected residual members keep their ordinary n_U
variables, with lower bound1; they are not subtracted as fixed constants.
Only root cones are counted as fixed offsets in equations below.

## 5. Bounds and nonlocal upper rows

The initial trace boxes are

    0<=n_U<=27,17,6,2,1 for |U|=0,1,2,3,4 respectively.

For nonempty U this follows from global incidence capacities and
simplicity. All empty-C residuals avoid any root cone; they form an
intersecting SF4 subfamily, since two disjoint such members and that
cone would be an empty-core sunflower. H27 gives the empty bound.
Assigned presence/absence and P10 emptiness refine these boxes.

If two fixed members A,B have U intersect A=U intersect B=A intersect B,
then every actual completion of U forms a sunflower with A,B. Both
fixed members lie in C union{x}, so hidden exterior points cannot change
the intersections. The source sets this coordinate's upper bound to0.
The residual completion is distinct from A and B: equality with one
would require that four-set to be contained in the other, impossible
for distinct uniform fixed members. Pairs of root cones can be skipped,
because their intersection contains x and a residual never contains x.
The source also rejects a sunflower already present among three fixed
members and contradictory presence/zero bounds.

For every represented point, pair or triple W, the incidence row is

    sum_{U superset W} n_U <= cap(|W|)-#{B in S_x:W subset B},
    cap(1)=17, cap(2)=6, cap(3)=2.

Every represented point is used: a core point lies in a root cone, and
the additional exterior point exists only when an actual marker uses it.
The imported minimum-degree theorem therefore gives the lower row

    sum_{U containing v} n_U >= 7-d_{S_x}(v).

At any fixed actual anchor A, its disjoint subfamily is intersecting,
and hence has size at most27. Subtracting the disjoint root cones gives
`disjoint-H27`. Since |F|>=68, at least41 members meet A; this is exactly
`actual-anchor-mu41` after subtracting the meeting root cones. The exact
nonempty proper A-trace classes have caps10,3,1 at sizes1,2,3; again the
fixed cones are subtracted once. The pair-degree19 rows are the universal
actual-anchor margin, with both endpoint incidences counted (including
two for a member containing both). The crowding26 rows apply to each
choice of three singleton coordinates on A and subtract their exact
fixed-cone contributions. Markers and assigned internals are actual
anchors, so the same rows apply to them without a root assumption.

The small-complete-core row counts every residual Q with
|Q intersect(Y union Z)|<=2, even if Q contains the represented exterior
point. If two such members were disjoint, their union would meet the
core in at most4 points. P10/P9 require at least3 points to hit every
block, while an intersecting I7/I8 has no common point and requires at
least2. Thus the union misses a root block in at least one component.
That cone and the two residuals give an empty sunflower. H27 applies.
The represented exterior point is deliberately absent from this test.

## 6. Whole-component pools and their precise guards

For v in Y or Z, write h_v for the residual members whose intersection
with that entire component is exactly{v}. Their three-point tails form
an intersecting SF3 family: if two tails were disjoint, their two
members and any root cone through v would form a sunflower with core{v}.
Thus h_v<=10.

P10 and P9 have a block avoiding every pair of component points. Hence
two members in different Y singleton classes cannot be disjoint: the
root cone on an avoiding block would complete an empty sunflower. The
whole Y singleton pool P is intersecting and P<=27. Its two distinct
centre tail families are cross-intersecting; their tails avoid both
centres. These are the explicit guarded cross15 hypotheses, giving
h_u+h_v<=15. The source also uses the ordinary consequences

    2P+7h_v<=110,
    P+5*1[s_v=9]+7*1[s_v=10]<=27

at each actual central anchor. These are the P10/P9 pool lemmas in
`D18-pool-research.md`, with their earlier proofs expanded in the full
D18 bridge; changing the global cap to17 preserves their hypotheses.

Z does not have an assumed two-point avoidance property. For a pair
u,v in Z the source installs a cross15 edge only when an actual fixed
B subset Z union{x} avoids both. Such B is disjoint from every member
of either singleton class except for possible exterior intersections,
which are absent since B lies in Z union{x}. If those two members were
disjoint they and B would be an empty sunflower. Their three-point
tails therefore satisfy the same guarded cross15 theorem. The union
of categories in any clique of these edges is intersecting; H27 gives
the clique row. Maximal cliques suffice, since all counts are nonnegative.
No unconditional whole-Z intersecting-pool premise is used for Q8 or I7.

At a literal C5 Y vertex, the pair pool consists of all residuals with
exact Y trace{v,w}. At a literal P5 Y vertex, let{a,b} be the unique
two-cover of its full four-edge graph. There are two separate pair
pools: one excludes partner a and the other excludes partner b. For
each specified pool b_v the ordinary pair/singleton lemma gives

    b_v<=6,       5h_v+9b_v<=59.

The code implements precisely these two restrictions for P5. It does
not apply the unrestricted C5 pair pool to P5. The two constituent
classes are disjoint from the singleton class, so updating their sparse
coefficient dictionaries does not overwrite a shared coefficient.

## 7. Universal local catalogue and complete graph filter

For each of the17 root anchors A={x,a,b,c}, use pair order
xa,xb,xc,ab,ac,bc, triple counts t_i indexed by the omitted anchor
point, and singleton counts s_i. Set

    k_i=1+sum_{j!=i}p_ij+sum_j t_j-t_i,       d_i=s_i+k_i.

The fixed root link determines the x-containing pairs/triples and s_x.
The three free pair counts range over0..3, the non-x triple count over
0..1, and each remaining singleton through the universal helper's range.
The seven recorded features are those three pairs, that triple, and
the three non-root singletons. For actual trace variables each feature
is the sum of n_U with the corresponding exact intersection with{a,b,c}.

`local_s_candidates` is called with `(emin,r10,r9)=(17,0,0)`, never with
a mu42 singleton bootstrap. Its universal predicates, and
`equality_consistent`, are necessary conditions on the actual state.
The other scalar tests are d_i>=7, d_i<=17, closed neighborhood
1+sum p+sum t+sum s>=41, all six d_i+d_j>=19, the universal mixed-trace
bound `(12,14,17,19,22)[#{i:s_i<8}]`, and crowding26 on the largest
three singleton counts. Each follows from an explicit imported result;
none assumes a finite exterior support.

At a Y anchor the root state is(s_x,k_x)=(7,10) for P10 and(8,9) for
P9. At a Z anchor it is(10,7) for I7 and(9,8) for I8. In particular
P10's s_x=7 does not activate B4 at x. The helper checks the complete
degree17 root identity rather than reusing a degree18 catalogue.

For a non-root v the known root cones give its **complete** point-link
graph at x inside L_v. Every triple through x belongs to the near family
K relative to the central anchor, since that anchor contains x. If
s_v>=8, B4 makes K intersecting; if d_v>=17, the high-link theorem does
so. For k_v in{7,8,9,10} its rooted graph must therefore occur in the
classified intersecting I_k. The filter compares the graph on all its
nonisolated vertices with every rooted graph in the relevant templates.
For k=7 it uses all eight H_i, including H7. For8 it uses all P10
eight-subfamilies and Q8; for9,10 the P10 subfamilies suffice.

The complete fixed root link guarantees that no extra x-point-link
edge is missing from this comparison. Isolated support vertices of K
need not appear in the point-link graph, so the graph test does not
assert equality of K's support with the graph support. Crucially the
test is guarded by s>=8 or d>=17: k=7 alone is insufficient. The
classified root component itself already supplies its actual root
geometry, so no additional root-neighbor graph test is needed at x.

## 8. Literal C5/P5 resource costs and singleton lower bounds

These cuts require a component support of exactly six points and a
complete point-link graph using all other five points. The code checks
that support equality, connectivity and the degree sequence. A five-edge
cycle is C5; a four-edge five-vertex path is P5 with its unique two-cover.
No such cut is inferred from edge count alone. They can apply to an I7
vertex if its literal graph passes the same check; a seven-point H7 or
Q8 component does not pass this six-point support test.

For each such vertex v, I_v counts actual four-sets inside the component
and through v. For P5, J_v counts those containing its unique two-cover,
so I_v-J_v is the source's removable count. For C5, G_v counts those
whose remaining three points cover every cycle edge. The unconditional
deletion lemmas give

    C5: d_v-G_v<=15,
    P5: d_v-I_v+J_v<=16.

The local row assigns the following nonnegative lower resource costs:

    C5: G_v >= max(0,d_v-15,k_v-5 if s_v>=8 or d_v>=16),
    P5: I_v-J_v >= max(0,d_v-16,k_v-6 if s_v>=8 or d_v>=17),
    P5: I_v >= max(1[d_v=17],k_v-4 if s_v>=8 and k_v>=8).

The unreachable d=18 cost4 is inherited harmlessly: the source's cap17
prevents such a state. At P5 and d=17, the only retained separated states
are(s,k)=(10,7),(9,8),(8,9). A P10 near component is impossible because
its complete x-point-link would have degree5, whereas the actual graph
has exactly four edges.

The k-4 cost deserves its support argument. With s>=8 the near family
K is intersecting. For k>=8 its complete P5 point-link rules out Q8 and
P10. A remaining P8/P9 near family uses six points, already including
the six distinct points in{x} union(component minus v). Hence these
supports coincide. Every one of its k-4 triples avoiding x therefore
lifts to a distinct actual internal four-set through v. It is enough
to prove this containment; the reverse inclusion is not asserted. This
argument is not applied at k=7 and makes no six-point assumption about
arbitrary I7.

For the removable k-6 bound, internal triples through the unique P5
two-cover can supply at most two extras alongside the four known
x-star triples. Deleting all other internals consequently leaves no
separated large near component of size at least7, which is also the
degree-minus-removable bound. The C5 costs follow from the analogous
cover completion lemma. These proofs depend on the full literal graph,
not on whether its parent component was labelled P10, P9 or I7.

Let h_v now mean the whole-component singleton count. The row's lower
value is0 for s<=7, at least6 for s=8,9 for s=9, and10 for s=10.
It becomes h_v>=s_v when the literal C5 has d>=16, the literal P5 has
d>=17, or s>=8 and k>=8. For s=9,10 and for an eight-member P-type
far family, isolation separates its support from the known star and
gives h=s. In the exceptional Q8 far case only its five-point core is
isolated; its six core-only triples are exterior, while leaf sharing
remains possible. This proves h>=6 at s=8 without a false h=8 claim.
In the guarded k>=8 case the same six-point support synchronization
and isolation supply equality. No singleton lower bound is inferred
for s<=7,k>=8 alone. The Y pairwise lower-cost pruning uses cross15,
so two retained lower values cannot have sum exceeding15.

For P10 Y, absence of all internals gives G=0. Thus d<=15, and B4
also gives k<=5 when s>=8. These stronger bounds are imposed only
on P10 Y. P9 Y receives the general cap17 and its actual resource costs.

## 9. Seven-point triangle-plus-path hubs

The separate hub test compares the complete point-link graph to a
triangle disjoint from a two-edge path and requires a seven-point
component. Its six nonisolated vertices are all other component points.
This recognizes the relevant Q8 or H7 hubs without assigning C5/P5
cuts to them. A three-point cover consists of two triangle vertices
and the middle of the path; consequently there are exactly three
possible actual internal cover completions through the hub. Let G
count their binary trace variables.

The ordinary complete-five-star lemma in
`D18-Q8-internal-research.md` proves

    d_v-G<=15,       s_v>=8 implies k_v<=5+G.

Deleting the completions preserves the literal five-star. A putative
degree16 sublink containing that star is separated by R16/B4; P-type
isolation forces all five prescribed star triples into a component
whose complete rooted graph is incompatible, or into a Q8 which
requires precisely the deleted completions. In the Q8/Q8 case the
cores avoid the opposite support and only leaves can be shared;
the degree5 hub cannot be a shared leaf. Thus the same contradiction
holds on arbitrary support. The proof uses the complete five-star,
not the label Q8 or a classification of the opposite I7.

The row encodes d-G<=15 by omitting the completion coordinates from
the incidence sum and subtracting the fixed root degree. Degree choices
are pruned by15+sum of their current upper bounds. For local states with
s>=8 the near size is pruned by5+that same upper sum. Since every actual
G is at most this sum, neither pruning removes an actual state.

## 10. Convex selectors and extension to the complete LP

For each actual root anchor the preceding tests retain its actual
seven-coordinate local state. Bucket pruning only discards a state
whose feature exceeds current trace lower/upper sums, whose resource
cost exceeds the current resource upper sum, whose degree is outside
the valid degree choices, or whose guarded hub near size is impossible.
None discards the actual state.

Choose the local selector of this actual row to be1 and all others0.
Then its normalization and seven feature equations hold exactly.
The weighted cost and singleton-lower rows reduce to the actual
inequalities in Sections 8–9; the conditional Y-pool row reduces to
its actual s_v case. A separate local copy at another anchor causes
no difficulty, because each copy can select that anchor's actual row.

If `degree_distributions=True`, additionally choose the selector for
each represented point's actual degree to be1. Its degree is between
the maximum of7 and the forced fixed-plus-lower incidence, and the
appropriate cap. The incidence/degree equation and every local degree
distribution identification hold. If these optional selectors are
disabled, the relaxation is weaker; actual feature sums still share
the same actual point degree. The absence of stronger distribution
ties cannot invalidate the family map.

All selectors have bounds0..1. An empty required local catalogue or
degree-choice set would contradict this existence argument for an
actual family, and its normalization equation correctly gives an
infeasible branch. The full model does not encode the single-component
ONE-HIGH row or every available member-sum consequence; those omissions
only weaken it and should not be described as installed constraints.

Consequently every family satisfying the stated branch premises
extends to an integral feasible point of the original projection,
with objective at least51. A correctly reconstructed certificate
bounding that objective strictly below51 excludes that conditional
branch. Branch coverage and each imported prior result remain separate
from the arithmetic certificate.

## 11. Exact-box interpretation and evidence limit

For a scaled upper certificate choose nonnegative integer weights y on
A z<=b and signed integer weights e on E z=f. Put q=A^T y+E^T e,
H=y.b+e.f, and let c be1 on trace columns and0 on every selector.
With integer scale D>0 and all coordinate bounds l_j<=z_j<=u_j,

    D*c.z <= H + sum_j max(l_j*(D*c_j-q_j),u_j*(D*c_j-q_j)).

This is an ordinary algebraic implication, independent of a numerical
solver's tolerance. Every trace and selector column must be included.
Strict comparison of the right side with51D is needed for this target.
The producer computes such an integer diagnostic from rounded dual
weights when its solver returns an optimal result. A status2 report by
itself is not an exact infeasibility certificate. Independent rebuild,
hash matching, integer coefficient/bound checks and exact summation
are still required for an independent replay claim.

No numerical exclusion of the eleven full forms is claimed by this
note. In particular, the source's explicit imports of reported P10
component gaps are not converted into replay evidence by this prose.

## 12. Separate v2: generic two-actual-anchor triangle inequalities

`D18-I06-triangle-closure.md`, SHA256

    3ae4598a645482695649bf484ac906cb14b08129d88310e44d92413f8f5c2c0b,

proves the following universal B4 consequence. Let R,M be distinct
actual four-sets with R intersect M={h,m}, choose k in R minus M, and
write the other R-only point as a and M minus R={b,c}. All six labels
are distinct. Let s be the exact m singleton count on R, p the exact
{k,m} pair count, and j the actual membership indicator of

    M'=(M minus{h}) union{k}={k,m,b,c}.

Then s+p-j<=12. Indeed, for s>=8 B4 makes the near family in L_m
intersecting. If p=3, its three residual two-sets are pairwise
intersecting (otherwise R closes a sunflower) and cannot be a three-edge
star (which would itself close a sunflower). They form a triangle.
Near intersection with M minus{m}={h,b,c} forces every triangle edge
to meet{b,c}; hence both b,c are triangle vertices and their edge
exists. Thus j=1 and p<=2+j. Together with s<=10 this gives the row.
For s<=7, p<=3 suffices. This uses neither mu41, the degree cap, nor
an I7/I8 classification.

The separate v2 source applies this to every ordered pair R,M in the
fixed actual collection with overlap size2, to either choice of m in
that overlap and either k in R minus M. Both root cones and selected
actual residual members can serve as anchors. There is no premise
that a free marker or free internal four-set is present.

For exact categories u={m} and w={k,m}, let

    offset=#{B in S_x:B intersect R is u or w}.

If M' contains x, its indicator is the known0/1 value
`int(M' in S_x)` because S_x is the complete root star. The projected
row has coefficient1 on every trace U with U intersect R in{u,w}
and right side12-offset+j. If M' avoids x, it lies wholly in the
represented C and its indicator is the binary full-four-trace n_M'.
Subtract1 from that coordinate's existing coefficient, and use right
side12-offset. Since M' itself lies in the pair category, this is a
cancellation of its positive coefficient, not replacement by-1.

All fixed offsets count only S_x. A selected residual member is still
counted in its trace variable exactly once. Because R,M lie in C
union{x}, all exact intersections are unchanged by unrepresented
exterior points. The companion is a four-set, and if it contains x
its root membership is known even when its other three points do not
form one of the displayed link blocks. These facts cover cone/cone,
cone/marker, marker/cone and marker/marker pairs uniformly.

Thus every actual feasible family point from Section 10 satisfies
the added v2 rows. The version records the theorem-note hash and the
original adaptation source among its dependency hashes. Its only
validation in this task is static syntax and source inspection; no
catalogue or model was executed to prepare it.

The prepared v2 source SHA256 is

    497f71f4fdf555c7456b42123684e7fd5059769f89662c257e2263425798b31a.

The original source and both prior classification/triangle notes retained
their recorded hashes. The v2 dependency list also hashes this bridge at
receipt generation. Static AST parsing succeeded; it establishes syntax
only, and no execution-based validation is claimed.
