# Local51 bounded formalization receipt

Task mode: formalize. Domain and binder order: `a b c e s t : Nat`. The theorem writes both degree expressions literally; no subtraction, division, coercion, or finite enumeration is involved.

The named root `FrontierLocal51.local_weight_le_51` proves the exact conditional weighted bound supplied for this task. The two small-degree implications, two large-coordinate implications, simultaneous-large implication, and degree-20 implication are theorem premises. Establishing these premises from geometry or set-family structure remains outside this Lean file.

The proof splits at `s ≤ 7`, `t ≤ 7`, and (in mixed cases) degree values 20 and 19, then closes each leaf with `omega`. The source was saved before its first and only compilation, which succeeded. Its transitive axiom closure is `propext`, `Quot.sound`; the explicit fail-closed allowlist also permits `Classical.choice`.

Attained grade: **axiom-audited**. This is a same-agent bounded check using the existing pinned dependency cache, not clean kernel replay or independent reproduction. Full command, source hash, output hash, elapsed time, runtime identity, and audit output are bound in `Local51.axiom-audit.json` and `Local51.bounded.json`.

The separate isolation audit retained exactly 16 existing actual theorem roots and passed. It omits the `AHS27SunflowerFree` module and the two corresponding construction roots; it makes no claim that their excluded checks completed.
