# Actual complementary-trace obstruction

Research formalization, 23 October 2026. No final review or publication.

`ComplementaryTraces.lean` proves a literal obstruction on arbitrary finite
sets: two nonempty disjoint tails lifted at a common point cannot coexist
with an actual outside cone containing that point. The three resulting
actual members would have identical pairwise intersection consisting of
that point. The statement keeps support disjointness, centre distinctness,
and actual membership explicit. It does not assume H27 or classify P9.

The two declarations `lifted_disjoint_intersection` and
`no_two_disjoint_traces_with_surviving_cone` compiled successfully on the
first bounded attempt. The observed transitive axiom lists contain only
`propext`, `Classical.choice`, and `Quot.sound`. The attained grade is
**axiom-audited**. The pinned existing dependency cache was used; no clean
rebuild or independent reproduction is claimed.

Source SHA256:
`7c26ba9f1d63d7edce06404b6bfeffbec1f73b4c6e93ccfbb584282e540467b7`.

Receipts are `receipts/ComplementaryTraces.bounded.json`, its `.log`, and
`receipts/ComplementaryTraces.axiom-audit.json`. The ordinary P9 application
still has to supply the displayed geometric hypotheses; this module alone
does not prove the complete complement bound or the global extremal bound.
