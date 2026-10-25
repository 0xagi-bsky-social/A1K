# Author response after complete round 3

All twelve actual round-three reviews are committed in public/round03/committed.json (round commitment f6adf56e50f0aafe7d62a132292b475ef9ff89162aeb7eb4c98c5efa8996d41f). This response proposes a repair; only actual reviewers can resolve their own findings.

## Maximum-degree root selection

The academic writer requested `/root/r67_writer:round-3:required-revision-1` (finding AW-ROOT-03). Section 5.2 now explicitly chooses a maximum-degree point: use a degree-6 point if one exists; otherwise choose degree 5 and impose global cap 5 only in those latter two branches. This is exactly the selection already stated in `highdegree/R15-rho6-finite-closure.md`, lines21–28. No finite domain, proof tree, degree bound or theorem conclusion changed. The old ambiguous sentence is retained in the frozen round-three manuscript and review record.

## Bounded checks and preserved qualifications

The completed reviews tested explicit counterexamples to omitted guards: complete C5 without internal cost, H27 without proved intersection, size16 classification without rho<=7, size15 support without rho<=6, selected cones without complete root degree, core-four exclusion without mixed-three exclusion, a homomorphism treated as complete blowup, deletion cardinality substituted for actual subset inclusion, and every-member substituted for an existential disjointness conclusion. The actual proof retains these guards. This summary is not a replacement for the reviewers' scoped checks or an assertion that all possible defects have been ruled out.

The data review's fresh corrupted-plan/receipt controls are archived byte-identically under checks/round03/data_analyst with a manifest. The original temporary paths and actual review JSON remain unchanged. The typesetter inspected all eleven round-three preview pages and explicitly acknowledged the earlier source-only link-parsing miss. These are preview checks, not final publication approval.

The new reproduction/README.md and manifest supply one actually rerun exact degree17 leaf using a pinned non-overwriting wrapper. Other listed command-line interfaces are inspected recipes, not newly claimed executions. Shared model construction and the ordinary/Lean distinction are retained.
