# Size-fifteen arithmetic interfaces

24 October 2026. Ordinary proof development, not final scientific review.

`R15ScalarClosure.lean` compiled on its first bounded attempt in3.455seconds under the existing pinned Lean4.26.0 environment. Five named roots passed fail-closed parsing of the actual compiler axiom output. Every root depends only on `propext` and `Quot.sound`, within the allowed list. The attained grade is **axiom-audited**, with an existing dependency cache; no clean-kernel-replayed or independently-reproduced grade is claimed.

The roots cover the outer-deletion budget contradiction, the strict ordered deficit triangle, the full three equality guards for hub deletion, the support-at-most-eleven numerical consequence, and the impossibility of maximum degree four under the size15 rho-six incidence count. All hypotheses are literal inequalities over natural numbers. In particular, geometric trace counts, the degree-two support reduction, finite proof trees and classification are not automatically formalized by this module.

The ordinary complete size15 theorem still has those distinct proof obligations. This module supplies exactly its stated arithmetic interfaces and no global extremal theorem.

Source SHA256: `df94065a7262c59b5cfb12544f173ed58af57ea3498b78329274992650200117`.

Evidence: `receipts/R15ScalarClosure.bounded.json`, `.bounded.log`, and `.axiom-audit.json`; executable fail-closed auditor `audit_r15_scalar.py`.
