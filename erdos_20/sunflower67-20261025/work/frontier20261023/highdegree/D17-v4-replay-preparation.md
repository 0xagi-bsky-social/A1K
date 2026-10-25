# Degree17 v4 exact replayer: preparation and added validation

23 October 2026. A new `replay_degree17_full_v4.py` is prepared from
the frozen v3 replayer

    replay_degree17_full_v3.py
    2e2238bfeb0ba50b98e74d4fe672ed58ee54d017b9a7387da15d875728863824.

No model import, model build, certificate replay, solver, census or Lean
command was run for this preparation. Static AST parsing and source
inspection are the present validation. The frozen earlier replayers,
producer versions and hashed ordinary notes are unchanged.

## Accepted versions and preserved checks

The explicit accepted producer hashes are the original degree17 full
producer, v2, v3 and the new v4

    a1beae56f60205a48442a1c6a31d2148557443511fb119a1936ffda8578bebf2.

All eleven root geometries retain root17, cap17, mu41 and target51.
The v3 optional-H27 adapter is enabled for both v3 and v4. It preserves
the separate literal-set compatibility/diagonal/witness verification,
the supported core-to-one-marker trace refinement and every resulting
sparse coefficient and right side. The unchanged generic triangle
validator applies from v2 onward. Older source versions must have no
named v4 B4 rows.

The new version also retains source and dependency binding, literal
premise and receipt identity reconstruction, separate binding of the
twelve prior P10 internal exact replays, complete integral matrix/box
validation, all-column Python-integer weighted arithmetic, explicit
trace-versus-zero objectives and strict target comparison. The one-case
deadline remains30 seconds. CLI receipt output refuses overwrite.

## Independent literal B4 row reconstruction

The new checker converts recorded root cones and selected actual
markers/internals to point sets. It does not call the producer's
`fixed_near_disjoint_witness` helper. For each actual anchor A and
v in A it finds the fixed members B through v whose tails B minus{v}
meet A minus{v}. It then looks for disjoint pairs of these tails.
This is equivalent to the ordinary B4 hypothesis in
`D17-marked-B4-addon.md`, using actual complete members only.

For every witnessed anchor/pivot it independently constructs

    sum_{U:U intersect A={v}} n_U
        <=7-#{B in S_x:B intersect A={v}}.

It requires exact row coverage, no duplicate labels, the literal
recorded witnesses, every sparse coefficient (including absence of
selector terms) and the exact root-star offset. The resulting row
collection receives its own hash in the replay output. The point-set
test includes marker anchors, represented exterior points and the
root pivot without imposing an ambient support bound.

## Evidence for local pruning from the final equations

Rather than calling the cached local catalogue or repeating its entire
`alive` computation, the additional checker reads the final equality
matrix. The local selector columns form its final17 contiguous blocks,
with sizes recorded in the receipt. Optional global degree selectors
occupy the preceding block and have their normalization equations
checked to determine the layout.

For each root anchor, the checker verifies its local normalization
and all seven feature equations: three exact pairs, one exact triple,
and three exact non-root singletons. Trace coefficients are rebuilt
from point-set intersections with the root-link triple. The remaining
coefficients must occur only in that local block; their negatives
decode the integer feature value of every surviving selector state.
Universal feature ranges0..3,0..1,0..10 are checked.

Whenever the independently found witness guards a non-root singleton,
every decoded surviving value must be at most7. For a guarded root
pivot, an exact root-star singleton count above7 requires an empty
local selector block. Empty catalogues are handled through their
zero-term normalization equation. The decoder accounts for all17
local blocks and the complete equality-row layout, including optional
degree-distribution tie positions. It hashes all decoded local feature
arrays and records each guarded coordinate, its witness, surviving
column count and maximum surviving singleton.

This proves a precise execution-level property when a replay passes:
every surviving local selector obeys the B4 pruning predicate, and
the direct B4 inequalities have the claimed literal family meaning.
It does not independently establish completeness of the unpruned
universal catalogue, prove that every other pruning predicate is
necessary, or reprove prior mathematical inputs. Those are covered
by the stated ordinary family-to-model bridges and shared-producer
reconstruction. The whole replayer is therefore not described as a
fully independent model implementation.

## Current status

The new source is ready for a separately scheduled one-case smoke
replay against a v4 receipt. No exact replay result or branch exclusion
is claimed by this preparation note. Later coverage of H0 internal,
mixed-four-core and mixed-three-core cases is a separate task; the
existence of this adapter does not establish that coverage.

Prepared v4 replayer SHA256:

    024c11d4897818233a74b7fff9f3c925ea521dd52818ec16411bd98ec3650b44.
