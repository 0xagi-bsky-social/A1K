# Degree17 P9 internal markers: independent four-orbit coverage

23 October 2026. This is an ordinary coverage bridge and a small independent
finite census, not a new LP run, full-model build, exact dual replay or Lean
proof. The separate checker uses only the Python standard library and imports
neither a projection producer nor any upstream checker.

Let the complete degree17 root link be P9(Y) plus an intersecting I8(Z),
on disjoint supports, under the hypotheses of `D17-full-model-bridge.md`.
The imported universal I8 classification gives the three opposite forms
P8-i1, P8-i2 and Q8. The displayed P9 is the canonical P10 with012 removed:

    015 023 034 045 124 134 135 235 245.

The independent `check_d17_p9_iy_coverage.py` checks all720 permutations
of six points against the literal P9 and P10 block sets. Their full
automorphism groups have orders6 and60. Its orbit calculation covers all
fifteen four-subsets of Y, with no omissions or overlapping orbits:

| Case | Representative | Mask | Orbit masks | Size |
|---|---|---:|---|---:|
| IY00 | 0123 | 15 | 15,23,39 | 3 |
| IY01 | 0134 | 27 | 27,46,53 | 3 |
| IY02 | 0234 | 29 | 29,30,43,45,51,54 | 6 |
| IY03 | 0345 | 57 | 57,58,60 | 3 |

It also independently partitions all45 pairs of P10 blocks under the
full60-element group to reconstruct the two canonical P8 deletion forms.
Q8 is supplied as its explicit eight triples on seven points. The
reconstructed complete root links are compared with every receipt.

Why are the same four internal orbits sufficient for all three Z forms?
An automorphism of P9 on Y, extended by the identity on Z and the entire
exterior, preserves the complete root link. It carries an actual internal
four-set to its displayed representative. Conversely, the product action
of the component groups restricts on a Y-internal set to the P9 action;
the Z action fixes that set. Thus the full component-product orbits are
exactly these four regardless of the opposite component.

If an actual family has any Y-internal member, choose one and apply such
a relabeling to the whole family. The corresponding `IY` case asserts
only that this chosen four-set is actual. It leaves all other Y and Z
internals free. It does not require a singleton internal assignment.
The marked member lies entirely in the represented core, so no exterior
support cutoff or exterior relabeling assumption is involved.

The twelve `*-IY*-internal-smoke-v2-*.json` receipts cover this four-by-three
product. The checker requires one receipt per pair, source v2

    497f71f4fdf555c7456b42123684e7fd5059769f89662c257e2263425798b31a,

root17, cap17, mu41 and residual target51. It rejects empty-Z, assigned-Z,
forbidden-trace and four-core exclusions, or a transferred P10-empty
dependency. It compares all four recorded IY orbits with the independent
set calculation, checks the root link, hashes the declared mathematical
dependencies and recomputes each producer premise fingerprint. Optional
degree-distribution selectors are mathematical consequences rather than
additional family restrictions; the current twelve receipts leave them off.

All twelve producer records have consistent reported integer scalars
H+correction strictly below51 times their scale. The largest reported
ratio is501629544370/10^10 in P9-P8-i1 IY03; the Q8 maximum is
491629544557/10^10 in IY03. These are reported certificate scalars.
The coverage checker does not recompute the weighted coefficient vector.
Exact dual verification belongs to `replay_degree17_full.py` and its
separately scheduled executions.

The independent finite coverage run completed in0.050 seconds and wrote

    degree17_full/P9-IY-active-v2-manifest.json
    SHA256 58d50a83f6dda67bffb1942c0b614d3c2aa4a125cf5fc4d2e8f5ee752f1a19f3.

The checker hash recorded in that manifest is

    7dc515ffdf4cd312ddbf8ee7ced8dfad8ecc1fbe5f295567cbedbe3ed6736af8.

Its status is `PASS_INDEPENDENT_IY_COVERAGE_ACTIVE_RECEIPTS`, with
`exact_replays_bound=false`. This names the exact current evidence level.
The script's optional `--bind-replays --output NEW_FILE` additionally
requires each already saved replay to be an unchanged-input PASS from
the frozen full replayer, bound to the same receipt, source, premise,
strict target51 numerator and checked triangle rows. It then writes a
new immutable manifest with exact-replay bindings; it does not execute
those replays. Existing output manifests are never overwritten.

Once all twelve exact replays are supplied, the ordinary family map
and this independent marker coverage exclude every P9-side internal
four-set in the three complete degree17 P9+I8 forms, conditional on the
stated imported theorems and global cap17. The present active manifest
does not itself assert that the twelve coefficient replays have finished,
and neither result closes all remaining degree17 branches.
