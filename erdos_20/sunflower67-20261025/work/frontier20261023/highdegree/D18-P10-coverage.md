# Independent D18 P10 + I8 marker coverage

23 October 2026. Ordinary proof-development support, not a final audit, LP arithmetic replay, or Lean proof. The checker `check_D18_P10_coverage.py` uses only Python's standard library and never imports a numerical producer.

The complete `D18-P10-active-manifest.json` selects exactly 123 receipts: 86 P8 receipts and 37 Q8 receipts. The independent checker reports `COMPLETE_CONDITIONAL_MARKER_CHAIN`: P8-i1 covers51/51 orbits, P8-i2 covers35/35, and Q8 covers37/37. The manifest SHA-256 is `41a906f71782390491b7e4ee001f5f97541703f593bad4403b4be2f10d9578df`. This is literal marker coverage and staged-premise validation; the dual coefficient replay is a separate task.

The separate `D18-P8-active-manifest.json` retains the original 86 v2 receipts: 15 Z-internal markers, 49 mixed-four markers, and 22 mixed-three markers. Of the 49 mixed-four cases, 43 have a recorded strict residual upper bound and six use hash-linked zero-objective phase-one certificates. A solver-only status2 receipt is not an active contradiction.

| Opposite component | Full component automorphism order | Z-internal orbits / sets | Mixed-four orbits / sets | Mixed-three orbits / traces |
|---|---:|---:|---:|---:|
| P8-i1 | 2 | 9 / 15 | 29 / 465 | 13 / 180 |
| P8-i2 | 4 | 6 / 15 | 20 / 465 | 9 / 180 |
| Q8 | 24 | 8 / 35 | 20 / 665 | 9 / 231 |

The P10 automorphism order is 60. The full link orders are consequently 120, 240, and 1440. The checker establishes this product description by reconstructing the triple intersection graph: its connected components have distinct sizes10 and8 and must each be preserved. It exhausts every permutation in S6 or S7 for the two component groups, including the Q8 leaves. The canonical exterior marker is fixed.

The P8 omission classification is reconstructed from all45 unordered pairs of P10 blocks. The two orbits have sizes30 and15, respectively, distinguished by whether the deleted blocks intersect in one or two points. Q8 is built literally from its six hub/core triples and two hub/leaf triples. The source theorem that every intersecting size8 SF3 family is P8 or Q8 remains an imported ordinary premise.

For each kind the checker constructs every internal Z four-set, every mixed four-set on the full core, and every mixed core triple together with one distinct exterior point. It recomputes every orbit representative and image, verifies domain disjointness and completeness, and compares all saved catalogue and receipt geometry with that reconstruction. The fresh marker represents an arbitrary actual exterior point by relabelling; it is not a finite ambient-support assumption.

## Explicit stage dependencies

The manifest has schema `D18-P10-coverage-v1`, a hash-bound `Y-internals-absent` ordinary bridge, and an ordered list of stages. A stage records `id`, `kind`, `depends_on`, and hash-bound `receipts`. Paths are relative to the manifest directory unless absolute. Only explicitly listed receipts are active. Listing a stronger source version or a successful-looking file in the directory does not activate it.

The P8 stages are:

1. All Z-internal marker exclusions, with no Z exclusions assumed.
2. All mixed-four exclusions, depending on the internal stage and hence justifying `empty_z`.
3. All mixed-three exclusions, depending on the mixed-four stage and hence justifying every `forbid_four_core` premise, including the prior Y-internal absence.

The Q8 stages have additional necessary ordering:

1. The four v2 internal exclusions I00/I01/I03/I07.
2. The three v4 HUB exclusions I02/I04/I05, using only the first stage's exclusions.
3. The v7 unassigned marked I06 triangle exclusion, using the previous seven exclusions. This completes all35 internal four-sets in eight orbits; no complete-pattern branch is active.
4. Nineteen v7 mixed-four exclusions, all assuming `empty_z`. E4_00 and E4_08 use their exact-negative phase-one receipts. E4_14 is omitted at this stage.
5. E4_14's v7 stage2 receipt, assuming the preceding19 mixed-four orbit exclusions. Its575 explicit forbidden four-sets are exactly those19 orbits; its marker has90 images. The saved strict bound is49.7058823605. The original bound50 receipt is inactive.
6. All nine v7 mixed-three exclusions, with `empty_z` and `forbid_four_core`, depending on the completed mixed-four stage. E3_05 and E3_07 use their exact-negative phase-one receipts.

The complete chain therefore uses ten phase-one receipts: six P8 mixed-four, two Q8 mixed-four, and two Q8 mixed-three. Its remaining113 receipts have strict residual upper bounds. The marker phases neither assume nor conclude that all proper core traces are absent.

Every explicit `forbidden` trace must be covered by the named ancestor stages. Receipts in one stage cannot justify each other's assumptions. Future, circular, and wrong-kind dependencies fail. A nonempty complete `assigned_z` branch is rejected by an ordinary marker stage. It is accepted only through the explicit complete-pattern extension described below.

A mixed-three exclusion means that no actual residual member has that exact three-point core trace, with any exterior completion. The checker therefore distinguishes a four-core absence from a mixed-three trace absence. The latter can justify either the corresponding three-coordinate trace or its four-coordinate version containing a named exterior marker. It cannot justify arbitrary pure triples, pairs, or other unsupported forbidden traces.

## Scalar receipt checks and remaining assurance boundary

The checker binds selected receipt bytes, saved producer source hashes, literal branch configurations, premise fingerprints, and all recorded orbit geometry. It checks the integer identity `H+correction=upper_numerator`, positive scale, strict `<50*scale` for a residual bound, or strict `<0` for a zero-objective infeasibility certificate. It also checks weight types/signs/row-index ranges. A phase-one receipt must bind its original status2 receipt and certificate producer by hash.

These operations do **not** reconstruct the model coefficients or the dual weighted sum. The exact arithmetic replay remains a separate task. Likewise the Y-internal ordinary bridge, all imported structural/crowding lemmas, the family-to-model map, and the terminal argument after marker exclusion are not proved by this coverage checker. The phrase “complete conditional marker chain” refers only to the marker geometry and dependency chain, conditional on those premises and the numerical certificates' separate replay.

The recorded run took less than one second and used no LP. Four deliberate manifest mutations were rejected: removing the internal dependency, bypassing the mixed-four dependency, creating a circular dependency, and changing a receipt hash. These checks did not import the numerical model.

Run the complete saved chain from the repository workspace:

```sh
python3 work/frontier20261023/highdegree/check_D18_P10_coverage.py --manifest work/frontier20261023/highdegree/D18-P10-active-manifest.json --require-complete
```

The default output is `D18-P10-coverage-diagnostic.json`. The complete run took0.30 seconds and reported no invalid inventory files. Without `--manifest`, the checker checks geometry and produces a non-authoritative receipt inventory. `--require-complete` requires all three kinds, including Q8. The P8-only manifest can still be checked with `--require-kinds P8-i1 P8-i2`; no Q8 closure is inferred from that smaller selection.

## Complete-pattern extension for the final Q8 internal branch

The active Q8 internal chain uses the strict v7 **unassigned marked** I06 triangle receipt. No complete-pattern receipt is active; the following pattern functionality is retained only for optional future branches.

A pattern stage adds two fields to the ordinary stage schema: a hash-bound `pattern_plan` and `remaining_internal_cases`, here `["I06"]`. The checker proves that the union of these case orbits is exactly the Z-internal domain remaining after the explicit ancestor exclusions. It then independently enumerates every subset of that bounded domain, rejects any literal sunflower with the18 fixed cones or other selected internals, and reconstructs the full-group assignment orbits. The implementation refuses domains larger than eight candidates.

For the six I06 candidates, all64 subsets yield49 sunflower-free labelled complete assignments. Their nine orbit sizes, including the empty assignment, are

    1,6,3,6,6,12,6,3,6.

These agree exactly with `degree18_p10/q8-I06-pattern-plan.json`, SHA-256

    99b691370ca1597ab0c461441841f8dfcbd519b9df1480470db840fab961af9a.

Every pattern receipt must have `case="none"` and a nonempty `assigned_z` equal to its canonical complete representative. The assignment's absences are branch restrictions justified by exhaustive assignment coverage; they are not prior global exclusions. Such a receipt refutes only that complete pattern. It does not mean that all internals are absent or that the whole Q8 branch is contradictory. Partial pattern stages record their closed and missing pattern IDs and contribute no individual I06 exclusion. Only when all eight nonempty assignment orbits have accepted strict certificates does the stage conclude that the remaining six I06 four-sets are absent. The empty assignment is retained for the later mixed-marker stages.

The previous partial pattern stage selected IDs3 and4 and correctly did not conclude I06 absent. It has now been removed from the active manifest in favor of the stronger unassigned v7 I06 receipt. Optional pattern runs and phase-one certificates are not dependencies of the current chain. No arithmetic replay is inferred from the geometric pattern checks.
