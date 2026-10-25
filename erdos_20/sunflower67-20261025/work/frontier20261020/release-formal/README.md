# Rank-four eighty endpoint: source proof bundle

Main root: `FrontierFinalEighty.rank_four_upper_eighty_of_intersecting_twenty_seven`.
It proves **I(27) implies G(80)**. I(27) remains a local ordinary hypothesis.
The ordinary corollary G(80) uses the explicit external computer-assisted I(27)
theorem in arXiv:2609.06175v1; this package does not certify that enumeration.

Unconditional structural root:
`FrontierTwoHighEighty.independent_twenty_stars_card_le_eighty`.
Two distinct noncooccurring degree-twenty points in a finite four-uniform SF3 family
force total cardinality at most eighty. No ambient support bound or I27 is assumed.

Sources are listed in topological order in source-manifest.json, with exact hashes.
The recorded closure has 161 modules: 63 freshly compiled and 98 source-matched prior
successful rebuilds. Root axiom audits were rerun in the rebuilt closure. Only
propext, Classical.choice, Quot.sound occur. Grade: axiom-audited. No independent
human certification or clean-toolchain replay is claimed.

To rebuild all 161 sources, provision Lean 4.26.0 and the exact package versions in
lake-manifest.json (mathlib 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67). Set LEAN_PATH
only to those external package olean roots and run:

    python3 rebuild.py --lean /absolute/path/to/lean

This command prepends its own new build directory, checks source hashes, then
compiles every module in topological order. It retains commands and outputs.
This is a reproducibility recipe, not an assertion it ran on another machine.
The observed-runtime.json records this task's actual installed paths.

See audit-logs for actual successful audits and rebuild-summary.json for the
recorded source-closure check. Exploratory cap 45, failed bitmask proof attempts,
and UNKNOWN SAT runs are outside this accepted source bundle.

Inherited A1K source provenance: 0e9aee578a7bb3dbc665630c759297514f88a81d.
Retained attribution/license files describe inherited upstream code; current
research sources are in the unprefixed modules under source/.
