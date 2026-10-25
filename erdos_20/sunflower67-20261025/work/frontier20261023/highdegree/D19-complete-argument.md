# Degree nineteen at the 68-member target

23 October 2026. Ordinary proof with exact integer computational leaves.
All statements below explicitly depend on the imported universal SF3
classification/isolations/trace facts, the separate complete-C5 obstruction,
and H27. This is neither an end-to-end Lean proof nor an unconditional claim
that M(4,3)≤67. Final review and publication remain closed.

## Claim and starting premises

There is no finite simple, four-uniform, three-sunflower-free family of size
68 with maximum degree at most19 and with a point of degree19, under the
listed imported facts. Empty-core sunflowers are forbidden. No support bound,
minimum positive degree, μ42 bootstrap or finite exterior universe is assumed.

The previous D20 proof excludes degree20 at this target. The universal SF3
upper bound20 then permits applying the present claim to any remaining
hypothetical family of size68. Together these branches give the necessary
condition Δ≤18 for such a family. Families with Δ≤18 have not been excluded.

The complete degree19 link is P10(Y)⊔P9(Z), on disjoint six-point supports.
Take Y=0,…,5, Z=6,…,11, and P9=P10 minus678. There are49 members avoiding
the root. Every actual anchor has closed neighbourhood at least68−27=41.

`D19-model-bridge.md` supplies the full family-to-model implication. Every
proper trace counts **all** exterior completions, with arbitrary labels;
binary bounds are used only for four-point traces. Local selector rows are
necessary universal anchor signatures, not a classification of all SF4
families. Ordinary structural refinements are proved in
`D19-singleton-I04.md` and `C5-internal-compatibility.md`.

## P9 internals are absent

The fifteen four-subsets of Z partition into I01,I02,I03,I04 orbits of sizes
3,3,6,3. The first three marked-member cases have exact residual upper bounds
48.0253164913,48.2022475785,48.5000002825, all below49. Their literal receipts
are `I01-none.json`, `I02-none.json`, `I03-cover-refined-none.json`.

The remaining three internal sets are {6,9,10,11}, {7,9,10,11},
{8,9,10,11}. They share the triple {9,10,11}, so at most two can occur.
Exactly one is excluded by `Zsingle-cover-refined-none.json` (bound48).
Exactly two are one orbit, excluded by
`Zpattern08-none-phaseone.json` (integer gap−251571517). Thus Z has no
internal member. In each assignment all other Z four-subsets are set absent
only after the preceding orbit exclusions or triple-cap argument justify it.

## P10 internals are absent

Direct augmentation against the ten P10 cones yields292 compatible internal
assignments in13 orbits: one empty and twelve nonempty. The complete orbit
coverage is independently reconstructed by `check_D19_coverage.py`.

`Ypattern03-Z.json` bounds the residual family by43. Ten further nonempty
orbits have exact negative-gap phase-one certificates, named
`YpatternNN-Z-phaseone.json` for NN=02,04,…,12. These certify the rebuilt
frozen v3 **necessary model**, not the original v4 floating-point run. The
source mismatch is explicitly recorded and harmless to the direct v3
family-to-model implication; the models are not falsely identified.

The remaining singleton internal pattern M={0,1,2,3} has exact upper bound49.
It requires an equality argument, not rounding a non-strict bound downward.
`check_Ysingle_equality.py` independently interprets the certificate as
seventeen unit-weight inequalities with total RHS48: every admissible trace
other than M has coefficient at least1 and M has coefficient0. Equality
forces d(3)=16, and a P10 automorphism preserving M forces d(1)=16. Complete
C5 geometry gives two cross-intersecting P10 tails, hence the same P10 tail.
The doubled-P10 lemma then gives |F|≤27+16+16−3=56, contradiction.
The full ordinary proof is `Ysingle-equality-proof.md`; the arbitrary-support
double-star lemma is `doubled-P10.md`. Therefore Y internals are absent too.

## Exterior marker exclusions and their order

With both interiors empty, the465 mixed four-point link traces and220
three-point link traces with a distinguished exterior point form28 orbits
under Aut(P10)×Aut(P9). All exterior points other than that distinguished
actual point remain unnamed and unrestricted.

Twenty-three direct marker cases have exact upper bounds below49:
E00–E08, E10, E12–E14, E16–E21, E23–E25, E27. The literal list and its681
forbidden traces on the enlarged13-point projection are in
`external-stage-exclusions.json`. This list is used only in the subsequent
stage, never circularly in its own certificates.

With those already excluded traces absent, E09 and E11 have exact negative
phase-one gaps, while E15 has upper bound45. The corresponding receipts are
`E09-staged-both-phaseone.json`, `E11-staged-both-phaseone.json`, and
`E15-staged-both.json`. The only surviving marked orbits are E22 and E26,
both pure Z triples plus one exterior point. All four-link-point traces and
all pure Y or mixed three-link-point traces are therefore absent.

## Ordinary terminal contradiction

Every residual now has at most two link-support points, except possibly
three points wholly in Z. Suppose two residuals Q,Q′ were disjoint. In each
of Y,Z their union must meet every component block; otherwise a missed cone
would be disjoint from both, giving an empty-core sunflower. Each component
has no transversal of size at most two, so the union needs at least three
points in each component. This is impossible under the remaining trace
shapes: if either residual has at most two link points, the union has at
most five; if both have three, both traces lie in Z and the union misses Y.

Thus the entire49-member residual family is intersecting, contrary to H27.
This strengthened terminal argument is in `D18-structural-tools.md`. It
needs neither the older mixed-pair cover lemma nor a weighted-deficit bound.

## Verification record and limitations

All43 necessary arithmetic receipts passed `replay_degree19.py`, including
the non-strict singleton bound whose equality is handled separately. Each
replay uses the exact frozen source hash, checks integral coefficients/RHS/
boxes and multiplier signs, and recomputes the full-column box correction
or infeasibility gap with Python integers. No solver is called by the replay.
This is **shared-builder exact replay**, not independent model construction.

`check_D19_coverage.py` uses literal masks/permutations and augmentation,
without importing a projection builder or numerical optimizer. Its saved
PASS covers all685 exterior markers, all staged forbidden traces, all15 P9
internals and all292 compatible P10 internal assignments.

The representation bridge, finite arithmetic replay, orbit coverage, and
ordinary equality/terminal lemmas are different evidence layers. The
external SF3 structural results and H27 remain imported ordinary premises;
they have not all been locally kernel-replayed. No whole-branch Lean theorem,
global novelty certification or completed global67 bound is asserted.
