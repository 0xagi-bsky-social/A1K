# Q8 E3 continuation and the ordinary terminal support bridge

24 October 2026. Ordinary development and phase-one plan integration.
No LP, coefficient replay or Lean process ran in this task. The parent
reported exact PASS replays for the two stage1 phase-one leaves; this
task prepared the additive plan from those named files. The separate
coverage checker remains the source of a checked whole-stage claim.

## Phase-one integration is already supported

The existing `prepare_d17_q8_e4_stage1_v9.py` accepts a phase-one
receipt through each `--completed-stage1-receipt` argument. Its strict
test detects `certificate_kind=zero-infeasibility`, requires positive
integer scale, the identity numerator=H+correction, and numerator<0.
The unchanged case, source, forbidden662 masks, empty-Z guard, literal
geometry and absence of extra actual members must all match. It does
not confuse a strict zero-objective gap with a residual upper bound.

The new immutable plan
`degree17_full/P9-Q8-E4-complete-plan-v9.json` was prepared with70
nodes. Its final two nodes use these active receipts:

* `P9-Q8-E4_56-exterior-E4-stage1-v9-84c78c6484a5-phaseone.json`;
* `P9-Q8-E4_57-exterior-E4-stage1-v9-17155df31d17-phaseone.json`.

Both nodes use exactly the same68 earlier nodes:12 internal nodes and
E4_00 through E4_55. Neither has its sibling as an ancestor. The prior
plan and all producer/phase-one/replay files are unchanged. The generic
stage checker additionally checks each phase-one source pin, its exact
original status2 receipt, preservation of all original model premises,
and the matching exact replay, so no additive phase-one adapter is needed.

## Exactly what must precede E3

Let the root be x=15 and let C=Y union Z, where Y={0,...,5} is P9
support and Z={6,...,12} is Q8 support. The complete core-four domain
has715 members:15 Y-internals,35 Z-internals, and665 mixed four-sets.
All715 must be justified absent before an E3 branch may set
`forbid_four_core=true`. The E3 scheduler explicitly checks this
inclusion in the facts returned by its antecedent-plan checker.

An E3 representative has three core points meeting both components
and one actual point outside C union {x}. Any residual member with
that mixed triple as its exact core trace has exactly one such exterior
point, because F is four-uniform and the member avoids x. Relabel this
one point as13, fixing C and x. All other exterior points remain free
and unrepresented; the model neither identifies them with13 nor bounds
their number. Thus exclusion of a representative under the component
automorphism group excludes every exterior completion of its entire
mixed-triple orbit.

There are231 mixed triples, since choose(13,3)-choose(6,3)-choose(7,3)
=286-20-35=231. The literal component-product automorphism census
partitions them into24 E3 orbits. The checker reconstructs that full
partition and checks its elements, not just the number24. Four-core
absence alone cannot replace any of these mixed-triple exclusions.

The current v9 E3 scheduler uses `empty_z=true`, the explicit15 Y
four-set exclusions, and `forbid_four_core=true`; all have antecedents
in the new completed E4 plan once its coverage check passes. It does
not need the optional v10 C4 bound to justify any of those premises.

## Ordinary terminal separation with unrestricted exterior support

Assume every core four-set and every mixed core-triple trace has been
excluded. Every residual member A in F_x^c then has exact trace
A intersect C of size at most2, or a pure three-subset of Y or Z.
This describes only its core trace, not its entire support.

Suppose two residual members A,B are disjoint. Their union must meet
every P9 block and every Q8 block. Otherwise the corresponding actual
root cone, which contains x and an avoided component block, is disjoint
from both A and B, producing an empty-core sunflower. P9 avoids every
subset of Y of size at most2. Q8 avoids every subset of Z of size at
most1. Consequently

    |(A union B) intersect Y| >=3,
    |(A union B) intersect Z| >=2.                       (1)

If neither member has a pure Y-triple trace, each uses at most two
Y points. To reach three Y points in (1), one member must use two
and the other at least one. The two-Y member has no Z point, because
a mixed trace of size3 or a core trace of size4 is excluded. The other
member has at most one Z point for the same reason. Their combined
Z trace has size at most1, contradicting (1).

Therefore one member, say A, has a pure Y-triple trace T. The other
must supply at least two Z points, and hence has no Y point: two Z
points together with a Y point would be an excluded mixed triple,
and a trace of size4 is also excluded. Since A union B meets every
P9 block, T itself is a three-point transversal of P9.

Remove all actual residual members whose pure Y-triple trace is a
transversal. The preceding proof shows that the remaining residual
family is intersecting, so its size is at most27 by H27. It is a
subfamily of the original SF4 family, and no support restriction is
needed for H27.

For P9=P10 minus012, its transversal triples are exactly its nine
retained blocks together with012 and345. This is a literal check of
the20 triples on its six-point support, independently performed by
the stage checker. Each retained block already occurs in its actual
root cone, leaving at most one residual completion by global triple
codegree2. Each of012 and345 has at most two residual completions.
Thus the removed family has size at most9+2+2=13 and

    |F_x^c| <=27+13=40.

Since the complete root degree is17, |F|>=68 would require
|F_x^c|>=51. This contradiction excludes the one P9-Q8 root-link kind
once its full E3 coverage is justified. Q8 needs no two-point avoidance
property; in fact its hub pair is a two-cover. The proof also does not
need pure-Z-triple exclusions, an ambient-support bound, or a full
independent classification of arbitrary intersecting SF4 families.

## Evidence boundary

The terminal reasoning is ordinary mathematics conditional on H27,
the global triple-codegree bound, the fixed actual P9/Q8 root link,
and the established absence facts. The marker orbit census and exact
leaf replays supply those absence facts in separate finite layers.
The preparation of the70-node plan alone is not the coverage result.
