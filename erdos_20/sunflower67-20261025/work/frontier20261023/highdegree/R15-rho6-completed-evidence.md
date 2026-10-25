# Completed ordinary and finite evidence for the size15 rho bound

24 October 2026. This append-only status note updates the pending small-check
boundary in R15-rho6-finite-closure.md without changing its hashed inputs.

The two degree2 finite reductions now have an independent reconstruction:
recheck_R15_degree2_support.py and R15-degree2-independent-check.json, status PASS.
R15-degree2-independent-ordinary-check.md independently verifies arbitrary-support
normalization, saturation of the fixed points, the whole-completion new-point
budget and the eleven-point moment bound.

The independent reconstruction recovered91 motifs in the degree6-neighbour
case and78 in the other case. It verified all literal witness/domain records.
In the second case it directly tested all74761 candidate six-subsets, importing
neither producer and using no DFS pruning; all have a forbidden pair together
with one fixed motif triple. No completion remains. Its source hash is
72482f0ce7cbb4990dba7df55958c41693ae85d5d7b332c062c881181ae0accd.

The three remaining size15 domains on eleven points have independent set-based
proof-tree replay PASS as recorded in R15-rho6-finite-closure.md and its three
replay receipts. Thus no finite obstruction in the rho<=6 route is currently
left unchecked by a separately written exact implementation. The mathematical
conclusion is the arbitrary-support universal statement

    |L|=15 and L simple SF3 => exists A in L with |D_L(A)|>=7.

This remains an ordinary computer-assisted proof. The small diagnostic lists
and proof-tree soundness are not formalized in Lean, and independent algorithms
or agent contexts do not constitute independent human certification. No global
originality or full rank-four extremal bound is claimed by this status update.
