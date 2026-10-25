# SmallTracePool source preparation

23 October 2026. `SmallTracePool.lean` was prepared without compilation, as requested while the root LP batch was running. Existing `TerminalSeparation.lean` and `TerminalAsymmetric.lean` are unchanged. No Lean validation or axiom report is claimed yet.

The module imports `TerminalSeparation` and works over an arbitrary type with decidable equality. It defines the actual finite subfamilies with trace size at most1 and trace size0, and the actual sum of support-trace cardinalities. It uses `disjoint_union_trace_ge_three` and `union_trace_card_le` to prove that the small-trace residual subfamily is intersecting. Uniformity and sunflower-freeness descend to that subfamily, so an explicitly supplied H27 hypothesis bounds its cardinality by27.

The independent counting theorem is stated for every finite family G:

    2|G| ≤ Σ(Q∈G)|Q∩W| + |smallTracePool G W| + |zeroTracePool G W|.

It follows by finite-set induction from the pointwise deficit identity for trace sizes0,1 and≥2. The literal residual specialization and the corollary giving at least11 empty-trace members from at least52 residuals, at most66 trace incidences and H27 are included. No component classification or exterior support bound is assumed.

Six `#print axioms` commands are ready for a later bounded compilation. The source contains no `sorry`, `admit`, axioms or finite `decide` enumeration. The root will schedule compilation separately.

## Observed compile and axiom check

The completed source compiled in3.63seconds aftertwo bounded repairs of Finset filter/empty-card simplification. Both failed attempts are retained in receipts/SmallTracePool.attempt1/2.{json,log}; they were rejected, not admitted. Allsix named root transitive axiom closures passed the exact allow-list {propext, Classical.choice, Quot.sound}. Evidence: receipts/SmallTracePool.axiom-audit.json. Attained grade **axiom-audited**, within the existing pinned dependency cache; notclean replay or independent reproduction. The initial source-only status above is superseded by this observed result. No global67 theorem or final-review gate follows.
