# P10 + I8 projection at degree 18

23 October 2026. This is a discovery constructor and its mathematical design
record. The source has been written without importing it, generating its
catalogues, building a model, or running a solver. This note makes no finite-case
exclusion claim and is not a final review, publication, or Lean result.

The file is `degree18_p10_projection.py`. Its explicit assumptions are a finite
simple SF4 family F with empty-core sunflowers also forbidden, |F| at least 68,
global point degree at most 18, and a point x of degree exactly 18 whose complete
link is a disjoint P10 and I8. It imports H27 and the universal local structural
statements used by the frozen `MU42/scripts/local43.py`, with `emin=17` and both
singleton bootstrap parameters zero. It does not import the old mu42 finite
exclusions, minimum positive degree four, degree-sum 52, pair-degree 20, or any
bound on the total support of F.

All internal four-sets on the P10 support Y are assumed absent. This is the new
mu41 P10-internal exclusion supplied separately by the twelve nonempty-case
receipts and their replays. The constructor does not independently replay that
dependency. Z-side internals remain free by default. Optional `empty_z`,
`assigned_z`, `forbidden`, and `forbid_four_core` arguments are extra branch
premises and are recorded literally in a receipt. An assigned Z pattern is a
complete pattern, so every other Z-internal four-set is absent in that branch.

The initial source was frozen as `degree18_p10_projection_v1.py` before the
complete rooted graph filter, HP16 rows, and optional degree-distribution
switch were added. The current file is the version prepared for scheduling.
The later prior-art cross15/crowding26 imports described below are enabled by
default and can be disabled together with `--no-crowding-imports`.

## Labels and complete marker orbits

P10 is the explicit family

    012 015 023 034 045 124 134 135 235 245.

The two P8 inputs are reconstructed by partitioning all 45 unordered pairs of
deleted P10 blocks under its full automorphism group, computed in S6. The
constructor checks that this group has order 60, that every pair belongs to
exactly one orbit, and that there is exactly one orbit of each intersection
size one and two. Their stable names are `P8-i1` and `P8-i2`; each representative
is chosen deterministically by its two block masks. This avoids reliance on an
earlier P8 label convention.

The third input, `Q8`, has hubs 0,1, triad 2,3,4, and leaves 5,6. Its six core
triples are a hub with two triad points, and its other two triples are 015,016.
For every I8 input, its full automorphism group is independently computed in S6
or S7, rather than assumed to be the stabilizer inherited from P10.

Y has labels 0 through 5. Z has labels 6 through 11 for P8, or 6 through 12 for
Q8. The distinguished root has label 15. A marked exterior point has label 12
in a P8 case and 13 in a Q8 case. These labels are distinct. The product of the
full component automorphism groups acts on Y and Z and fixes the exterior
point. The components have sizes 10 and 8 and are not exchanged.

The marker catalogue has three separately checked domains:

- `I00`, ...: every Z-internal four-set;
- `E4_00`, ...: every four-core set meeting both components;
- `E3_00`, ...: every mixed three-core set with the one actual exterior point.

Each orbit is checked to stay in its domain, to avoid previously covered
orbits, and to exhaust its domain. The union is checked to contain every
four-core set except the fifteen already excluded Y-internal sets, and every
mixed-three-core-plus-exterior marker. There are 660 raw marked sets for either
P8 input (480 four-core sets and 180 mixed triples), and 931 for Q8 (700 and
231). These raw counts are elementary binomial counts; this note does not
claim that the program's orbit computations have been executed.

The marked exterior point is retained throughout the projection. In
particular, its degree, its exact intersections with other members, and its
contribution to actual-marker anchor constraints are not collapsed away.
Every residual of either requested marker type can be moved into this list by
an actual component automorphism and, when needed, renaming its one exterior
point. This justifies using one representative per orbit, conditional on the
catalogue coverage checks passing when the code is first run.

## Actual traces and the relaxation map

Let S be Y union Z, together with the marked exterior point when the marker
uses it. For every subset t of S of size at most four, the variable n_t counts
the actual members Q avoiding x with Q intersect S equal to t. The unknown
points outside S are unrestricted. Proper trace variables are counts, not
Boolean variables, and two different members with the same trace remain two
members. Only four-point traces have upper bound one, by simplicity.

Their initial upper bounds, by trace size, are 27,18,6,2,1. The empty trace is
disjoint from any prescribed central anchor and therefore has bound 27 by
H27. The other bounds follow from point/pair/triple incidence and simplicity.
The total number of residual members is exactly the sum of all n_t. No finite
exterior universe is introduced by these definitions.

Each selected four-point marker is an actual member and is forced to one.
The source rejects a sunflower among selected members and the prescribed
cones. For any pair of such fixed members, it also zeros a residual trace
whose three actual pairwise intersections would agree. Both fixed members
lie in the represented universe with x appended; consequently these tests
remain exact even when the residual trace has unknown exterior completions.
The source does not impose unsupported sunflower tests between two unmarked
proper traces, whose exterior intersections are unknown.

For each represented point, pair, and triple, the global incidence rows have
capacities 18,6,2 and subtract the actual contributions of the eighteen fixed
cones. Selected residual markers remain among the n_t variables and are not
subtracted a second time.

Every cone and selected marker is an actual four-member anchor. At each one,
the model includes exact proper trace caps 10,3,1, a disjoint-member H27 row,
the closed-neighbourhood lower bound 41, and all six pair-degree sums at least
19. These are constraints on counts of actual members. The last two bounds
use the contradiction premise |F| at least 68: H27 gives the first, while
the second follows from

    |N[A]| <= d(u)+d(v)-d(u,v)+23,
    d(u,v) >= 1.

The objective maximizes the residual count; there is no residual lower row.
Thus an exact upper bound below 50 contradicts the size-68 premise. Constraints
such as mu41 remain explicitly conditional on that premise even in this
relaxation, whose points of smaller objective need not themselves correspond
to smaller actual families.

With the prior-art crowding import enabled, each actual anchor also receives
the four inequalities saying that each three of its exact singleton classes
sum to at most 26. Contributions of the known cones are subtracted exactly.
This is equivalent to bounding the three largest singleton classes by 26.
The corresponding central local states are pruned by that same condition.

## Central local rows and shared degrees

At each cone A={x} union T, the three exact pair classes containing x, the
three exact triple classes containing x, and the exact singleton class {x}
are fixed by the complete root link. The remaining local coordinates are
three pair counts, one triple count, and three singleton counts. They are tied
to seven buckets of the same global n_t variables.

The constructor enumerates the necessary `local43` states with root degree
18, cap 18 at the other three points, mu41, pair-degree 19, the universal
trace-margin table, and the imported equality-consistency test. It also
checks the root's own `local_s_candidates` condition. No bootstrap lower
bound on the near component of a singleton-9 or singleton-10 state is used.

There is also a complete rooted graph filter. Whenever s>=8 or d>=17, the
near family K is intersecting by B4 or the universal high-degree separation.
If k is 8,9,10, the imported classification makes K a P8/Q8, P9, or P10.
Every triple containing x is in K, since x belongs to the local link anchor.
The entire point-link graph at x in K therefore equals the prescribed graph
`{T\{v}: v in T in L_x}`. The constructor canonically compares this graph on
its nonisolated vertices with the graphs at every used point of every P10
k-subfamily and, for k=8, Q8. A mismatch rejects the local row. It does not
assume that the support of K equals its point-link support. At k=7 there is no
filter or I7 classification. This also handles Q8's triangle-plus-P3 hub graph
without treating it as a C5: such a near family can have size eight but not
nine or ten.

Global trace incidence already shares actual point degrees at the level of
means. Optional `degree_distributions=True` adds one degree-selector
distribution for each represented actual point and ties every central anchor
through it to that same distribution and its global incidence. The default is
False, because these additional distribution equations can slow the LP.
The stronger option is valid because an actual family chooses one degree and
one local row at each anchor. Relaxing these choices to convex weights enlarges
the feasible domain. Core points have the minimum degree already supplied by
their fixed cones; the marked exterior point only has the degree forced by
its selected member. There is no universal positive minimum-degree premise.
The degree-15 cap on Y is a consequence of its literal C5 and the explicit
Y-internal-empty premise.

## Optional local geometry used conservatively

A point is classified as C5 only if its complete literal point-link graph is
a connected five-cycle on all other five points of a six-point component. It
is classified as P5 only if that complete graph is a connected four-edge path
on those five points. The graph must exhaust the component minus the point;
being a subgraph or having the right number of edges alone is insufficient.

The Q8 input has seven points and none of its vertices receives these cuts.
Its possible high-degree local states are governed by the universal
`local43` conditions, the complete rooted graph filter, and the other general
constraints. In particular the
constructor does not exclude a size-eight Q8 near component with a size-ten
opposite component at degree 18.

For a literal C5 vertex v, let G_v count internal four-members through v whose
other three points cover the cycle. The source uses d(v)-G_v at most 15, and
the conditional cost G_v at least k_v-5 when s_v is at least 8 or d(v) at least
16. With no Y internals this gives d(v) at most 15 and k_v at most 5 in its
large-singleton states. It uses the full-C5 theorem, including its size-16
exception analysis, rather than a universal size-16 split assertion.

For a literal P5 vertex, let I_v count all component-internal members through
v, and J_v those containing the unique two-point path cover. It uses

    d(v)-I_v+J_v <= 16,
    k_v <= 6+I_v-J_v     if s_v>=8 or d(v)>=17.

The supported high-degree states are (s,k)=(10,7),(9,8),(8,9) at degree 17,
and (10,8),(9,9) at degree 18. A P10 near component would give the root point
degree five in that component, whereas this literal point-link gives four.
The source also charges I_v at least one at degree 17 and at least four at
degree 18. When s_v>=8 and k_v>=8, B4 makes the near family intersecting, the
literal P5 excludes Q8, and its six-point P-type support is exactly the six
already prescribed points. Therefore I_v>=k_v-4. No arbitrary I7 is classified.

For every vertex that passes the literal six-point C5/P5 check, h_v denotes
the whole-component singleton count. It is bounded below by 6,9,10 for central
singleton size 8,9,10 respectively. The Q8 core/leaf argument gives six, not
eight, in the first case. The source uses h_v=s_v only in the established
C5-degree-16, P5-degree-17, or s_v>=8 and k_v>=8 regimes. The six-point support
check makes the same proof applicable to a C5/P5 vertex of a P8 component.
No such lower row is added at a Q8 vertex, and no h>=s-2 rule is assumed at
s<=7 merely from k>=8.

The ordinary proofs and their dependencies are in `D18-structural-tools.md`.

## Shared P10 singleton and pair pools

Only Y receives the whole-pool H27 bound. Write h_y for the exact Y-singleton
count, P=sum h_y, and b_y for all exact Y-pair traces containing y. The source
includes

    h_y<=10,   P<=27,   b_y<=6,   5h_y+9b_y<=59,
    2P+7h_y<=110.

It adds all fifteen pair-pool rows for distinct y,z in Y. With the default
prior-art cross15 import, these are `h_y+h_z<=15`. With that import disabled,
the fallback is `h_y+h_z<=16`. The latter uses the ordinary near-doubled-P10
proof in `D18-pool-research.md` under |F|>=68 and Delta<=18, not the aggregate
pool bounds alone. HP16 is weaker than the prior-art result and is not claimed
as a frontier improvement. The matching lower-pool sum test removes a central
Y row whose two established h lower bounds exceed the applicable bound.

It also includes, at each central anchor through y,

    P + 5 Pr(s_y=9) + 7 Pr(s_y=10) <= 27.

The probabilities are the local convex selectors. They are valid because
h_y=s_y at sizes nine and ten. These penalties are not added together across
different points. The source does not impose the nonconvex pair/singleton
table as a false linear cut, nor does it transfer the P10 pool argument to an
arbitrary I8 with a possible two-point transversal.

## Prior-art cross15 and crowding26 imports

The frozen paper's crowding section, `paper/main.tex:968-1024`, proves under
mu>=41 and Delta<=18 that the three largest exact singleton classes of any
actual anchor sum to at most 26. Its cross-star ingredient has the exact
guards needed by the Y pools: two distinct centres outside both tail
supports, intersecting tail families, cross-intersection between the families,
and actual four-set lifts in the same SF4. If their total is at least sixteen,
it produces an actual anchor with neighbourhood at most

    d(a)+d(b)-d(a,b)+4 <= 40,

contradicting mu>=41. Hence the applicable pool inequality is HP15.

These are imported prior-art statements with both written arbitrary-support
reductions and finite certificate dependencies. The existing Oct20
`FOUNDATION_LEDGER.md` records normal and optimized replays of both
`terminal.cross15` and `terminal.crowding`, bound by
`replay-selected-20261020/RECEIPT.json`. They have not been rerun in this task.
Normal and optimized executions of the same checker are not independent
mathematical verification. The code records hashes of the written paper,
both certificate files, both checkers, the ledger, and the prior replay
receipt whenever these imports are enabled.
It also binds the current `prior-delta18-unlock.json`, which records the
parent's match of the present package and saved outputs to those prior
replays. The CLI accepts explicit `--crowding-imports` as well as its default.

The explicit degree-cap-18 premise is essential to this use. The imports do
not silently add the further minimum-degree-seven or support-23 claims;
their separate rooted bridge is not used by this constructor. No new result
is claimed from rediscovering the weaker HP16 argument.

## Execution and evidence boundary

The default CLI action prints a catalogue and does not solve. An explicit
`--build-only` builds one relaxation. An explicit `--solve` runs one case with
a solver time limit of at most 30 seconds; model construction time is recorded
separately. Examples for later scheduling are

    python3 degree18_p10_projection.py --kind P8-i1 --catalogue
    python3 degree18_p10_projection.py --kind Q8 --case I00 --build-only
    python3 degree18_p10_projection.py --kind P8-i2 --case E3_00 --solve --seconds 30

No example was executed while writing this source and note. The first
scheduled run should allow its explicit finite group and coverage checks to
complete before using any case labels. The orbit lists and component labeling
are included in a numerical receipt.

The only executed source checks were standard-library AST parsing and
existence checks for the imported certificate/checker paths. The constructor
itself was not imported. An initial `python` command was unavailable;
`python3` performed the successful syntax checks.

An optimal numerical result is rounded at scale 10^10. The source uses Python
integer arithmetic on all columns, including all local and degree selectors,
to compute q, weighted RHS H, and the finite-box correction to the objective.
It records the nonnegative inequality and signed equality weights, the exact
numerator, the target 50, and source/local43/structural-note/pool-note hashes.
Receipt filenames contain the kind, case, an optional human label, and the
first twelve characters of the hash of all source hashes and literal premises;
the full premise hash is also stored. This is an
exact diagnostic of this constructed conditional relaxation; it is not an
independent model reconstruction or a Lean certificate. A status-two solver
response alone is recorded as numerical infeasibility, without an exact
infeasibility certificate. Existing receipt files are not overwritten.

The intended branch work is to exclude the represented four-core and mixed
three-core markers. The parent research has a separate ordinary terminal
argument bounding the remaining residuals by 37 after these exclusions; that
argument is not encoded as a premise or claimed to have been established by
this constructor. No pure-triple exclusions are needed in this planned stage.
