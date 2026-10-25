# Terminal separation: formalization status

23 October 2026. Assurance: **axiom-audited** for the seven roots listed below, under the existing pinned dependency cache. This is ordinary proof development, not a final review, a clean replay, or an independent reproduction. No global size-67 theorem is claimed.

`TerminalSeparation.lean` imports only the existing `AHS27Data` module. Its mathematical roots are polymorphic in an arbitrary ground type `α : Type u` with decidable equality. Families and members are finite sets, so duplicates are excluded. They use the project's literal `IsSunflowerFree F 3`, which forbids empty-core sunflowers as well. No ambient cardinality bound, maximum degree, complete centre link, finite classification, or old numerical certificate is assumed.

The data are a four-uniform family F, a centre x, two disjoint finite supports Y,Z, and supported component block families HY,HZ. Every block's cone `insert x T` is an actual member of F. The `TwoAvoidance` structure requires every subset of either support of size at most two to be disjoint from some corresponding block. The residual family is defined as `F.filter (fun Q => x ∉ Q)`; it is not an arbitrary surrogate for F's residuals.

The proved roots are:

| Lean declaration in `FrontierTerminal` | Proved conclusion |
|---|---|
| `disjoint_union_trace_ge_six` | Two disjoint residual members use at least six points of Y∪Z in their union. |
| `residual_intersecting_of_trace_le_two` | If every residual trace has at most two support points, all residual members intersect. Mixed pair traces are permitted. |
| `disjoint_terminal_pair_opposing` | If both traces have size at most two or are pure triples on one support, a disjoint pair must be opposing pure transversal triples. |
| `residual_intersecting_of_no_pureY` | Traces of size at most two or arbitrary pure Z triples force the residual family to be intersecting. |
| `residual_card_le_27_of_trace_le_two` | The first intersection result gives residual cardinality at most 27 under the explicit H27 hypothesis. |
| `residual_card_le_27_of_no_pureY` | The one-sided pure-triple case gives residual cardinality at most 27 under H27. |
| `terminal_separation_card_bound` | Under general pure-triple terminal geometry and H27, `r ≤ 27 + min(|T_Y|, |T_Z|)`, with T_Y,T_Z defined as the actual residual pure-transversal subfamilies. |

The additional intermediate theorem `small_union_intersects` gives the stronger pairwise interface: at most five points of Y∪Z in the union of two residual members forces their intersection. `terminal_without_pureY_intersecting` proves that deleting the Y pure-transversal subfamily leaves an intersecting family; the terminal count applies the same result after exchanging Y and Z.

The public definitions are substantive: `PureTriple` means the **entire** support trace has cardinality three and lies in the specified component. `PureTransversal` adds that this exact trace meets every corresponding block. H27 is an ordinary supplied proposition quantifying over all four-uniform sunflower-free intersecting families on α; it is not introduced as a Lean axiom. It appears only in the cardinality corollaries. `terminalTrace_literal` verifies the expanded trace restriction, and `not_twoAvoidance_empty` checks the empty-block-family edge case.

The proof constructs a literal three-member empty-core sunflower if a disjoint residual pair misses a prescribed block. Uniformity ensures the two residuals are nonempty and hence distinct; the cone is distinct because it contains x. The small-set avoidance hypotheses then give three union-trace points in each disjoint support. All remaining trace classification and counting steps are symbolic finset arguments.

Two bounded compiles were run, both successful, with zero repair cycles. The first compiled the structural theorems and the direct count corollaries in 4.65 seconds; the second added the general terminal count and compiled the complete module in 5.20 seconds. Both used the existing `compile_bounded.py` wrapper, Lean 4.26.0, `-j1 -M512`, and a 120-second process deadline. No other Lean module was compiled, no solver or enumeration was run, and no old large `decide` computation was invoked. Existing imported objects were reused.

The final compiler log prints each of the seven root axiom closures. All seven are exactly

    propext, Classical.choice, Quot.sound

The fail-closed receipt parser required exactly these seven named outputs, successful compilation, an unchanged source, the recorded log hash, and an axiom subset of that allow-list. It recorded PASS in `receipts/TerminalSeparation.axiom-audit.json`. The compiler receipt and complete output are `receipts/TerminalSeparation.bounded.json` and `receipts/TerminalSeparation.bounded.log`. The final source, object, runtime-manifest, import-source, import-object, and log hashes are bound in the audit receipt. The compiler reported only four style/unused-variable warnings, with no errors or placeholders.

There are no open obligations inside the named roots. Applying the theorems to the D18/D19/D20 research branches still requires proving the corresponding cone-containment, component avoidance, and residual trace restrictions. The universal H27 premise must also be supplied for cardinality conclusions. Neither those branch exclusions nor a universal improvement to 67 is claimed by this module.
