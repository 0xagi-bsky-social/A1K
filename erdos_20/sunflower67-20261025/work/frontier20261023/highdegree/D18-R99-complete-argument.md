# The degree-18 P9⊔P9 branch at cardinality68

23 October2026. Ordinary mathematical argument plus exact computational leaves.
The universal SF3 classification, B4/isolation/trace capacities, separate C5
obstruction, and H27 are explicit imported premises. The new universal
terminal-separation lemma has a local Lean proof; the entire branch does not.
This is not a claim that the unrestricted extremal bound is67.

Assume a finite simple SF4 family F has68 members, global maximum degree≤18,
and complete link at x equal to P9(Y)⊔P9(Z) on disjoint six-point supports.
Each P9 is P10 minus012, transported onto its support. The residual family
avoiding x has r=50 members. Every actual anchor has closed neighbourhood
at least41 by H27. Arbitrary ambient support is allowed throughout.

## Necessary model

The complete family-to-projection proof for D19 in `D19-model-bridge.md`
applies with root/maximum degree18, residual50, and both components P9.
In particular actual-anchor pair-degree sums remain≥19, not18: μ≥41 and
the exact10/3/1 trace caps prove this independently of the degree cap.
Rooted P5 high-link restrictions and the d−I+J≤16 correction apply on both
components. No μ42, positive minimum degree, or support bound is used.

The four additional row families in the strengthened model are proved in
`D18-R99-bridge.md`: HP16, the affine external-pool inequality, lower bounds
on actual whole-component exterior pools, and conditional pool bounds.
Their ordinary geometric proofs are in `D18-pool-research.md` and
`D18-structural-tools.md`. The Q8 leaf exception is retained: a size8 central
singleton guarantees only six whole-component exterior triples unless a
separate disjoint-support argument justifies all eight.

The unsuccessful v2 model with extra degree-distribution selector ties
is retained as an experimental timeout; no conclusion relies on it.
The active v3 omits those ties and uses the necessary shared trace variables.

## Internal sets

Under the72 component automorphisms and exchange, the30 internal four-sets
form four marked-member orbits of sizes6,6,12,6. It is enough to mark one
internal member; the other internal choices stay free.

I01 and I03 have exact residual bounds48.7807878284 and49.7. Their complete
orbits are then forbidden in the next stage. With those already justified
absences, I02 and I04 have exact bounds48.2857154138 and49.9332448196.
All four bounds are strictly below50. Therefore both interiors are empty.
The staged assumptions are saved in `degree18_r99/internal-stage1-exclusions.json`.

There is an additional catalogue-free equality proof for the original
I02 bound50 in `D18-R99-I02-equality.md`. It is optional in this proof chain:
the strengthened strictly-below50 certificate already excludes the case.
The equality proof forces two identical P10 exterior tails and contradicts
the doubled-P10 counting lemma. It does not round a non-strict bound down.

## Four link points, then mixed three link points

With interiors empty,465 remaining four-subsets of Y∪Z form22 orbits.
Each actual marked member has an exact residual bound below50, recorded in
`E00-fourcore-both.json` through `E21-fourcore-both.json`. The largest is
47.666666676. Thus no residual lies wholly in the link support.

Only at this point are all495 four-point link traces forbidden. The180
mixed three-point link traces, each with its actual exterior fourth point
distinguished, form8 orbits. Their receipts are
`E28-mixed-both.json` through `E35-mixed-both.json`; the largest exact bound
is48.628241723, again below50. All further exterior labels remain arbitrary,
and proper traces retain integer multiplicities rather than binary bounds.

`check_R99_coverage.py` independently reconstructs the72-element group,
all30 internal sets, all465 mixed four-sets and all180 mixed triples. It
checks that every staged forbidden trace comes from the preceding exclusions.
It imports no numerical projection builder or optimizer.

## Ordinary terminal contradiction

Every residual now meets Y∪Z in at most two points, or in a pure triple on
one side. The terminal separation lemma gives

    r≤27+min(|T_Y|,|T_Z|),

where T_Y,T_Z are the actual pure-transversal residual subfamilies.
For each P9 there are eleven triple transversals: its nine blocks, its
deleted P10 block, and that block's complement. The nine prescribed blocks
have at most one residual extension each because their cones already use
one of the triple-codegree capacity two. The two complementary exceptions
have at most two extensions **together**: if opposite triples had distinct
exterior extensions, those two members and a cone on the other side would
be disjoint. Consequently |T_Y|,|T_Z|≤11 and r≤38, contradicting r=50.

The general arbitrary-ground-type separation statement is axiom-audited
in `../formal/TerminalSeparation.lean`, root
`FrontierTerminal.terminal_separation_card_bound`. The concrete P9
transversal count and complementary-extension step are ordinary proofs here;
they are not silently included in that Lean result. The terminal argument
allows mixed pair traces and does not need a further mixed-pair exclusion.

## Evidence and boundary

All34 active exact arithmetic receipts have passed
`replay_degree18_r99.py`, tied to the matching frozen v1/v3 generator and
local43 hashes. The replay invokes no solver, checks integer matrices/RHS/
boxes and multiplier signs, and recomputes all-column box corrections with
Python integers. It shares the producer's model constructor; the ordinary
model bridge and the separately written coverage check are distinct layers.

This excludes only the P9⊔P9 degree18 case under the stated imported facts.
The P10⊔I8 cases and every lower-degree case remain separate obligations.
Final scholarly review and three-format publication remain closed.
