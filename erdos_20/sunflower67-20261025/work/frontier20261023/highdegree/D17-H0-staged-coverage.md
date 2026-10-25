# Degree17 P10 plus H0: staged coverage and conditional terminal assembly

23 October 2026. Ordinary proof development and independent finite marker
coverage. This note does not run an LP, rebuild a projection model, replay
a dual certificate or invoke Lean. Its conclusion is conditional on the
explicit exact-replay and coverage checks below; it is not a closure of
all degree17 links or a global size67 theorem.

## 1. Family and fixed source hypotheses

Let F be a finite simple four-uniform family with no three distinct
members having equal pairwise intersections, including empty cores.
Assume |F|>=68, global maximum degree at most17, and a point x of degree17
whose complete triple link is the disjoint-support union

    P10(Y) disjoint-union H0(Z).

Use x=15, Y={0,...,5}, Z={6,...,11}. The unshifted component triples are

    P10: 012 015 023 034 045 124 134 135 235 245,
    H0:  012 034 134 035 235 145 245.

H0 is the actual row0 of the frozen universal I7 certificate, SHA256

    fe172301b201819c029d9a1b7e8931f516cbd90aa978977118b7853b2ead7164.

The independent checker compares its literal block set to that row and
checks that it is an intersecting SF3 family on six points. The general
arbitrary-support I7 reduction and the fact that this is one of the
eleven complete degree17 forms are the separate prior inputs in
`D17-I7-classification-route.md`. The present branch needs only this
explicit H0 geometry, not a new finite universe assumption.

The root has exactly17 cones, so the residual family R of members
avoiding x has cardinality at least51. The relevant projection source
hashes are

    v3 d247fa0ac29e5ea765f5ede2d60df9ff9ce89e905f86f1295161acedceb370ae
    v4 a1beae56f60205a48442a1c6a31d2148557443511fb119a1936ffda8578bebf2.

Their ordinary family maps are `D17-full-model-bridge.md`,
`D17-H27-clique-addon.md` and `D17-marked-B4-addon.md`, with the stated
H27, small-uniformity, B4, high-link, local43, crowding and minimum-degree
imports. All unknown exterior completions retain their exact-trace
multiplicities. The global degree17 cap is supplied conditionally and
does not assume that a separate degree18 computation has finished.

## 2. Stage zero: P10-side internals are absent

The separate degree17 component exclusion supplies this premise through
the twelve nonempty P10 internal orbits P10_001 through P10_012. The
already completed exact replay summary is

    degree17-replay/P10-nonempty-summary.json
    d130fb5c8f164e4ab6a164e60bd1c2e8f41021da82f48195255a3cc11690711c.

Its producer and replayer hashes are, respectively,

    1e3eaa89225246bb695740792bcaf0a5c365eb50c4212467aeb3c9569d7658d0
    1e6ef9e322b31593e12483a1e53937bf950f424d8c29433793f40ed98198608a.

The staged checker binds the summary, every original/replay pair and
their dependency files. It requires all twelve PASS results, matching
root17/cap17/mu41/minimum7/bootstrap0 and exact negative gaps. Their
nonempty orbit sizes total291 out of292 compatible assignments in13
orbits under Aut(P10) of order60. These are existing component replay
bindings, not fresh coefficient replays by the coverage checker.

The component proof uses exactly68 members. To apply it to F with
|F|>=68, retain all17 root cones and all actual four-sets inside Y,
at most15 further members, and extend to a68-member subfamily. The
complete root link, global cap and entire Y-internal assignment are
preserved. Thus any nonempty Y assignment would contradict the exact68
component exclusion. This gives Y-empty without restricting Z internals.

## 3. Independent literal marker domains

`check_d17_h0_stage_coverage.py` imports no producer or upstream checker.
It checks all720 permutations of six points against the literal P10
and H0 blocks. The complete automorphism orders are60 and6. Their
product group of order360 acts independently on Y and Z and fixes a
canonical actual exterior point12 when one is used.

The independent domains and orbit counts are:

| Stage | Literal domain | Domain size | Orbits |
|---|---|---:|---:|
| IZ | all four-subsets of Z | 15 | 4 |
| E4 | all mixed four-subsets of Y union Z | 465 | 14 |
| E3 | all mixed three-subsets of Y union Z plus point12 | 180 | 6 |

Each orbit is generated from the least remaining mask under the full
literal product group. The checker requires the orbits to be disjoint
and to have exactly their stated domain as union, and compares every
representative and entire orbit with all receipts' geometry metadata.

The IZ representative masks are960,1728,1856,3648, with orbit sizes
3,3,6,3. The E4 representatives are

    71 75 195 449 519 523 579 643 705 897 1539 1601 1793 3585,

with orbit sizes

    30 30 45 6 30 30 45 90 36 18 45 36 18 6.

The E3 representatives are4163,4289,4611,4673,4737,5633, with orbit
sizes45,18,45,18,36,18. These lists describe marker coverage; they
are not an enumeration of the ambient ground set or exterior families.

If an actual residual member lies in one of these domains, relabel the
whole family by the component automorphism carrying its core trace to
the representative. In E3 its one actual exterior point is additionally
renamed12; it is distinct from x because the member is residual. This
relabeling preserves the complete root link and all prior stage
absences. No symmetry of F itself is assumed.

## 4. The three-stage implication

First use the four `H0-internal-v3` IZ leaves. They assume only Y-empty,
with all other Z internals free. The selected IZ marker is actual;
it is not a complete singleton internal assignment. If every one of
their exact certificates excludes residual51, every Z internal is
absent by the four-orbit coverage.

Next use the fourteen `H0-fourcore-v4` E4 leaves. They assume Y-empty
and Z-empty but do not impose four-core absence. Their selected mixed
four-core marker is actual and other mixed four-sets remain free.
Excluding all fourteen removes every mixed four-core member. Together
with Y-empty and Z-empty, this removes all four-core residual members.

Finally use the six `H0-mixedthree-v4` E3 leaves. They assume Y-empty,
Z-empty and absence of every four-core residual. The selected mixed
three-core trace plus its actual exterior point is present. Excluding
all six removes every residual with mixed three-point core trace.

The checker enforces this order and these exact switches. In every
leaf `assigned_z=None` and `forbidden=[]`; no unlisted complete internal
pattern or trace exclusion is permitted. The four-core switch is false
in IZ/E4 and true only in E3. The empty-Z switch is false only in IZ.
Each leaf's Y-empty registry must equal the separately bound twelve
degree17 component inputs and exact gaps. Optional degree-distribution
selectors add only valid coherence constraints; no new family premise.

The H27-clique input is a literal hash-bound mathematical consequence,
not an additional absence assumption. The coverage checker binds its
bytes and dependencies and checks that declared witnesses are actual
root cones or the selected member. The exact replayer separately
checks all clique pairs and diagonals, actual witnesses and any
core-to-one-marker trace refinement. V4 exact replays also check the
literal cap7 B4 rows and surviving local-selector pruning.

## 5. Active certificates versus completed replay evidence

There are24 active leaves: four IZ, fourteen E4 and six E3. The unique
active certificate for E4_11 is the `-phaseone.json` descendant of its
original numerical status2 receipt. It has explicit zero objective and
reported exact gap-1666666667. The phase-one producer hash is

    929a101c2ec29570790450d112914f2048a83c78fdf8b5f658f84cb7f4eb8069.

The checker binds the original input path/hash and producer, requires
unchanged original model/premise metadata, and compares its reported
numerator strictly with0. The superseded status2 input is preserved
as provenance but is not counted as an active exact certificate.
The other23 leaves use the trace objective and require a strict
reported numerator below51 times their integer scale. Consistency
of the reported H+correction is checked without recomputing its
weighted coefficient vector in this coverage script.

Default checker mode additionally requires every active leaf's saved
exact replay to be PASS with unchanged inputs and the same source,
premise, objective, numerator and target. It accepts the frozen v3
replayer for v3 leaves, or the new v4 replayer for either source:

    v3 replay 2e2238bfeb0ba50b98e74d4fe672ed58ee54d017b9a7387da15d875728863824
    v4 replay 024c11d4897818233a74b7fff9f3c925ea521dd52818ec16411bd98ec3650b44.

Missing, unfinished, nonstrict or mismatched leaves/replays cause
failure. No partial closure manifest is written. The explicit
`--active-only` mode still requires all24 completed strict producer
certificates and binds all12 prior component exact replays, but labels
its result active-only and sets `exact_leaf_replays_bound=false`.
Its existence must not be reported as completion of leaf arithmetic.
Every manifest has a fresh output path; existing files are not overwritten.

At preparation, the six E3 producer records are present and report
strict bounds, while the coordinating task is carrying out the24
exact leaf replays. This note does not declare that batch finished.
A default-mode exact-bound manifest is the later explicit completion
evidence, and the note remains a conditional assembly independent of
the batch's wall-clock status.

## 6. Conditional terminal bound r<=37

Assume the three stages have been established. A residual member then
has core trace of size at most2 or a pure triple in Y or Z. P10 avoids
every subset of Y of size at most2, so a transversal has size at least3.
H0 has no point common to every block, so a transversal has size at
least2. The checker verifies both finite literal properties. No
transversal-number-three assumption about H0 is needed.

If residual members Q,Q' are disjoint, their union must hit every block
in each component. Otherwise a missed root cone and Q,Q' would be a
three-petal sunflower with empty core. Thus their union has at least3
Y points and at least2 Z points.

Suppose neither member has a pure Y triple. To obtain at least3 Y
points, one has two Y points and therefore no Z point, since all
mixed three-traces and four-core traces have been removed. The other
has at least one Y point and can have at most one Z point. Their Z
union would have size at most1, contradiction. Hence one member Q
has a pure Y triple T. The other must have at least2 Z points and,
by the same allowed-trace conditions, no Y points. Therefore T itself
hits every P10 block.

The triple transversals of P10 are exactly its ten blocks, a further
literal property independently checked here. Let A be the residual
members whose core trace is one of these blocks. Every disjoint pair
in R has an endpoint in A, so R minus A is intersecting. H27 gives
|R minus A|<=27. Each P10 block already has its root-cone completion;
global triple codegree at most2 allows at most one additional residual
completion. Thus |A|<=10, without any bound on exterior identities.
Consequently

    r=|R|<=27+10=37.

This contradicts r=|F|-17>=51. It is the general asymmetric terminal
argument of `D18-pool-research.md`, Section8, applied with H0 having
the required one-point avoidance property. The separate arbitrary-type
formal module `../formal/TerminalAsymmetric.lean` expresses that
terminal pattern with H27 as a supplied hypothesis; no new Lean claim
is made by this coverage task.

Therefore the stated P10+H0 degree17 branch is excluded once the
24 exact leaf certificates and their independent staged coverage
are bound successfully, conditional on the explicitly imported prior
theorems and component exclusion. Other H_i and P9 branches are outside
this assembly.

Prepared independent coverage-checker SHA256:

    f6a153caa9cb75b2c27157f4d3b8b154d7abea54d910eac70f796a8fe0b8130c.
