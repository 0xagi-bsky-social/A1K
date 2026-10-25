# Asymmetric terminal separation: formalization status

23 October 2026. The five root theorems below are **axiom-audited** in the existing pinned dependency environment. This is ordinary proof development. It is not a final review, clean replay, independent reproduction, or a global bound of 67.

`TerminalAsymmetric.lean` imports the existing `TerminalSeparation` module and leaves that module and its object unchanged. It reuses the actual definitions of `residual`, `HasCones`, `TwoAvoidance`, `TerminalTrace`, `PureTriple`, `PureTransversal`, `pureTransversalMembers`, `Intersecting`, and the explicit hypothesis `H27`. It adds `OneAvoidance`, which requires supported blocks and a block disjoint from each support subset of cardinality at most one. The empty-subset case ensures the block family is nonempty; `not_oneAvoidance_empty` verifies that edge case.

All root statements quantify over an arbitrary `α : Type u` with decidable equality. F is a finite simple four-uniform family satisfying the project's literal `IsSunflowerFree F 3`, including empty-core sunflowers. The component supports Y,Z are disjoint, and every HY/HZ block has its cone at x in F. HY satisfies `TwoAvoidance` on Y; HZ only satisfies `OneAvoidance` on Z. The permitted residual traces on Y∪Z are of size at most two or pure triples entirely in Y or entirely in Z. No support cutoff, complete centre-link hypothesis, point-degree cap, size condition on F, or classification of I7/I8 is used.

The proved roots, in namespace `FrontierTerminal`, are:

| Declaration | Conclusion |
|---|---|
| `asymmetric_disjoint_union_trace_ge_five` | A disjoint residual pair has at least five union-trace points in Y∪Z: at least three in Y and two in Z. |
| `asymmetric_disjoint_terminal_pair_has_pureY_transversal` | Every disjoint terminal pair has an actual member whose complete support trace is a pure-Y transversal triple. |
| `asymmetric_without_pureY_intersecting` | Removing the actual pure-Y transversal subfamily T_Y leaves an intersecting residual family. |
| `asymmetric_terminal_separation_card_bound` | Under explicit H27, `r <= 27 + |T_Y|`. |
| `asymmetric_terminal_residual_card_le_37` | With the additional explicit bound `|T_Y|<=10`, the residual cardinality is at most 37. |

The structural proof first uses the existing literal empty-core sunflower construction to show that a disjoint residual pair's union meets every component block. The two avoidance hypotheses give the different thresholds three and two. Both small traces would have union size at most four; pure-Z traces cannot supply the required three Y points. Hence a pure-Y triple must occur. Its partner must supply two Z points, so the permitted-trace restriction forces that partner's entire support trace into Z. The pure-Y triple alone therefore meets every HY block. The deleted subfamily is a defined filter of actual residual members, not a free family or a premise already asserting separation.

H27 is used only after the removal theorem establishes intersection. The final size-ten hypothesis bounds this actual removed subfamily. The module does not assert that every component satisfying `TwoAvoidance` has only ten transversal triples. Applying the size-37 corollary to P10 requires the separate P10 transversal description and the triple-capacity argument with its existing central completion. Applying the structural result to P10+I7 or P9+I8 requires verifying the stated avoidance hypotheses; the theorem itself does not use or assume an I7 classification. A different verified bound on T_Y can be substituted in the general counting theorem.

One bounded compile succeeded in 3.96 seconds, with zero repair cycles. The command was the existing `compile_bounded.py TerminalAsymmetric`, which invokes Lean 4.26.0 with `-j1 -M512` and a 120-second process deadline. No other Lean module was compiled, and no solver or enumeration was run. The only compiler warnings were two unused-section-variable style warnings.

All five printed transitive axiom closures are exactly

    propext, Classical.choice, Quot.sound

The fail-closed audit required exactly the five named output records, successful compilation, unchanged source, the recorded log hash, and all axioms within that allow-list. It also checked that the imported TerminalSeparation source and object retain their pre-task hashes. The resulting receipt is `receipts/TerminalAsymmetric.axiom-audit.json`; compilation and complete output are in `receipts/TerminalAsymmetric.bounded.json` and `receipts/TerminalAsymmetric.bounded.log`. These bind the final source/object, imported source/object, runtime manifest, and compiler output.

No proof obligations remain open inside the named roots. Branch-specific residual trace exclusions, component avoidance, and the numerical bound on the actual transversal pool remain application obligations, rather than being inferred from this terminal lemma.
