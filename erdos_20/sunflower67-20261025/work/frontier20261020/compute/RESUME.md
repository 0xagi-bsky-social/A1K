# Compute / bridge recovery state

- `ProfileABridge.lean`: previously elaborated; `ProfileABridgeAudit.lean` passed. Converts actual Profile A into `ResidualProfileA` without adding a nonrealizability premise.
- `ProfileAFibers.lean`: elaborated on recovery (32.48 seconds). Roots `row_key_card_two`, `key_card_two`, `fiber_card_le_four`, `rows_card_le_four_mul_keys`.
- `ProfileAFibersAudit.lean`: all four roots passed transitive axiom allow-list audit (5.04 seconds), only `propext`, `Classical.choice`, `Quot.sound`. Receipts in `receipts/ProfileAFibers{,Audit}.json`, with immutable timestamp copies. Assurance: `axiom-audited`, not independent replay.
- `compile.py` now invokes Lean with `--memory=1024`, timeout 120 seconds; timeout becomes recorded exit 124, not a theorem or counterexample.
- Numerical upper 45 for universal two-star residual was already checked by Python and independent C++; no need to rerun. It is certificate-diagnostic until a full Lean bridge and certificate are proved.
- No scholarly final review or publication has started; user gate requires genuine new research result first.

## Further universal bridge

`TwoStarResidual.lean` elaborated (5.16 seconds) and `TwoStarResidualAudit.lean` passed both roots (3.61 seconds): only `propext`, `Classical.choice`, `Quot.sound`.

`FrontierTwoStarResidual.residual_meets_link_support_ge_three` says that in an arbitrary ambient type, any 4-uniform SF3 family containing two centers with 20-member links and no member containing both has every member omitting those centers intersect the support of either center's link in at least three points. No support cap, canonical form, or numerical experiment enters the theorem. This is a useful representation bridge, not the still-open universal cap 45.

The proof uses the inherited sharp minimum transversal six for a twenty-link and the new disjoint residual-row outsider budget. If R had two outsiders relative to x-link support, every y-star row (which contains the outsider y) would have to meet R. Then R would be a four-point transversal of the twenty-link at y, a contradiction.

## Analytic closure route for Profile B (in progress)

New target: any 4-uniform SF3 family with two independent degree20 centers and all other degrees at most19 has size at most80. Delete both stars, obtaining H. Let U,V be the two 12-point link supports and q=|U∩V|. Each residual row meets U,V in ≥3 points, hence meets U∩V in ≥2. Residual degrees are at most14 on U and9 on U∩V. Thus 3|H|+5q≤168 and2|H|≤9q, yielding37|H|≤1512 and |H|≤40. This does not use support17, the unique degree18 point, I27, or finite cap45 diagnostics.

`TwoStarBridge.lean` now elaborated (4.14 seconds) with exact family/degree partitions, high codegree5, and residual degree bounds. `a_close_3` owns generic incidence arithmetic in theory/TwoHighIncidence.lean. Next: assemble universal80 and literalProfileB exclusion, then audit.

## Profile B closed

`TwoHighEighty.lean` elaborated successfully (3.71 seconds). Named roots:
- `FrontierTwoHighEighty.two_independent_high_card_le_eighty`: two independent high centers, all other degrees≤19 ⇒ family.card≤80; arbitrary universe, no support-size restriction and no I27.
- `FrontierTwoHighEighty.exactly_two_high_card_le_eighty`: exactly two high points and every member contains at most one high point ⇒ family.card≤80. The other-degree bound follows from the inherited unconditional degree≤20 theorem.
- `FrontierTwoHighEighty.profile_b_not_realizable`: literal `¬ Erdos20V13Boundary.ProfileBRealizable`, no mathematical premise.

`TwoHighEightyAudit.lean` PASS all nine new bridge/terminal roots (5.15 seconds); only standard three allowed axioms. Attained grade `axiom-audited`. Parent informed. The argument uses no numerical cap45 experiment. Unrestricted f(4,3)≤80 still additionally requires Profile A exclusion and I27 (external known result or local formal proof).

## Frozen final universal corollary

`FrontierTwoHighEighty.independent_twenty_stars_card_le_eighty` added and elaborated (3.80s), all10 roots audited (5.50s), standard3 axioms. Its only assumptions are finite4-uniformSF3 family, distinctx/y, degree20 at both, and no member containingboth. The previous other-degree≤19 premise is derived from inherited unconditional highPoints.card≤2. No I27 or ambient support bound. `source-freeze.json` binds all owned Lean sources; no further edits planned.
