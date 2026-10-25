# P9–Q8: ordinary copy check and explicit stage continuation

24 October 2026. Ordinary proof/model development, not final review. Numerical execution and exact replays are assigned to the parent task. This note does not promote producer diagnostics to proofs.

## Separate copied-block bounds

I checked `D17-P9-copy-cross15.md` against the actual-star hypothesis recorded in `PRIOR_DELTA18_UNLOCK.md`. The argument is valid conditional on that imported HP15 theorem, finite simple SF4, mu at least41, and maximum degree at most18.

Write H=P10 minus B on six points Y, C=Y minus B, and let x be the actual nine-tail centre. For another actual centre z outside x+Y, retain only those T in H+B whose z-lift is actually present. Every pair of retained triples intersects, including pairs involving B; the same holds with C replacing B. Each family is SF3 because its lifted members are SF4 at their common centre. Both are cross-intersecting with H, and both centres are outside both tail supports. HP15 gives nine plus the retained count at most15. These are separate inequalities; B and C cannot be pooled without an additional argument. The ten template triples are distinct. Full four-point traces z+T count literal members, not possible completions, and no x-cone contributes an offset.

The stronger IZ04 fallback also checks. Here Q={8,9,10,11} is actual, and the surviving opposite cone has tail U={6,7,12}. A member with exact Z-trace {12} avoids Q. The family disjoint from Q is intersecting: two disjoint members together with Q would be an empty-core sunflower. Consequently this member meets every xH cone. P9 avoids every pair of Y points, so it must use at least three Y points; its fourth point is12. Its Y triple is among the eleven transversal triples H,B,C. Copies of both B and C at12, together with x+U, would have common pairwise intersection {12}; they are forbidden. Thus all members of this pool lie in one of the two separate HP15 families, and the pool has size at most6. This does not assume a global Q8 pool is intersecting, restrict exterior support, or require Y internals to have vanished.

## Explicit internal dependency DAG

Four independently replayed IY leaves provide the15 Y-internal exclusions. Initially no Q8 internal is absent. The active IZ leaves and their exact antecedents are:

| Leaves | Producer / stage | Earlier IZ orbits required | Total forbidden core four-sets |
| --- | --- | --- | --- |
| IZ01, IZ03, IZ05, IZ07 | v4 / stage0 | none | 15 |
| IZ00 | v6 / stage2 | 01,03,05,07 | 33 |
| IZ02 | v6 / stage3 | 00,01,03,05,07 | 36 |
| IZ06 | v8 phase-one / stage3 | 00,01,03,05,07 | 36 |
| IZ04 | v9 / stage4, producer upper48 | 00,01,02,03,05,06,07 | 48 |

IZ02 and IZ06 are siblings: neither stage3 leaf uses the other. The phase-one IZ06 leaf binds its original status2 receipt and frozen v8 phase-one source. The seven already saved IZ diagnostics were strict, but their exact replay files were absent at this inspection. During preparation the parent supplied `P9-Q8-IZ04-internal-Z-stage4-v9-cba75ba7b396.json`, SHA256 `a761d6eb9c04357cfbfc6f06f9bc59ace8b0e0d191c30387bd09103ac15c6204`, whose producer integer numerator is480000000000 at scale10000000000. It is now pinned in the plan preparer. Its own exact replay remains necessary before contributing the final two Q8 four-sets. A rounded objective equal to51 is not an exclusion.

Every `uses` edge in the prepared plan points backwards. Complete automorphism orbits are propagated as facts; a leaf's forbidden masks must be contained in earlier facts. Absence of a four-set never implies absence of its proper subsets. Neither a progress counter nor a file named `forbidden` supplies a proof antecedent by itself.

## Exterior and terminal census

The actual core is Y={0,...,5}, Z={6,...,12}; root x=15 lies outside it. The canonical exterior marker is13. P9 has six automorphisms (extend uniquely by its omitted degree-four-point triple to P10); Q8 has24, independently permuting its two hubs, three triangle vertices and two leaves. Their product has144 elements.

There are15 Y four-sets and35 Z four-sets. The remaining core four-set domain has binomial(13,4)-15-35=665 members; mixed core triples have binomial(13,3)-20-35=231 members. The stored catalogue partitions these into58 E4 and24 E3 orbits; its eight IZ orbit sizes are3,2,6,12,2,1,6,3. The new checker retains the literal permutation/orbit reconstruction rather than accepting those reported orbit counts as coverage. No new census was executed during source preparation.

After all internals are justified, an E4 leaf may set `empty_z=true` and forbid the15 Y four-sets. E3 leaves additionally require every one of the665 mixed core four-sets to have been excluded before setting `forbid_four_core=true`. The one actual exterior point is relabelled to13; no global ambient-support limit is introduced. Residual trace multiplicities keep every other exterior point unrestricted.

After all core four-sets and mixed triple traces vanish, the ordinary separation argument in `D17-generic-stage-plan.md` applies. Remove residual members whose pure Y triple is a transversal of P9. Its nine actual root blocks permit one residual completion each; the missing block and its complement permit two each by triple-codegree2. At most13 members are removed. The remaining residual family is intersecting, bounded by27 via H27; hence r<=40<51. Q8 need only avoid every single Z point for this terminal argument; no unsupported two-point avoidance is used.

## Prepared tooling boundary

The old P8 v6 driver cannot be extended by changing its allowed-kind list alone: its internal logic only admits stages0/1, while Q8 needs the DAG above and a v8 phase-one leaf. Likewise its plan preparer and checker need explicit v8/v9 source and replay adapters.

The new files prepared alongside this note keep all prior sources immutable. Their default actions only prepare an explicit plan or inspect required antecedent metadata. Numerical/replay commands are emitted or run only under their explicit CLI actions, one bounded subprocess per case. No adapter, producer, solver, coefficient replay, or Lean job was executed in this preparation task. Exact receipt replay, independent literal orbit coverage, and this ordinary bridge remain separate assurance layers.

The prepared files are `prepare_d17_q8_stage_plan_v9.py`, `check_d17_stage_plan_v9.py`, `run_d17_plan_replay_v9.py`, and `run_d17_q8_exterior_stage_v9.py`. The preparer uses exact named receipts, not a newest-file search, and can append named E4/E3 progress lists. The coverage checker extends the frozen v6 checker with exact v7/v8/v9 source/replayer/phase-one adapters and requires the corresponding complement-profile/copied-tail validation evidence. Nonempty extra-member branches remain unsupported. The exterior scheduler checks the supplied explicit plan and all existing exact replays before importing any producer; it itself imports only the standard-library literal checker. Each producer is a separate bounded subprocess.

Suggested parent-controlled sequence, from this directory:

```text
python3 prepare_d17_q8_stage_plan_v9.py --output degree17_full/P9-Q8-internal-plan-v9.json
python3 run_d17_plan_replay_v9.py degree17_full/P9-Q8-internal-plan-v9.json
python3 check_d17_stage_plan_v9.py degree17_full/P9-Q8-internal-plan-v9.json --allow-partial --output degree17_full/P9-Q8-internal-coverage-v9.json
python3 run_d17_q8_exterior_stage_v9.py --plan degree17_full/P9-Q8-internal-plan-v9.json --stage E4 --case E4_00
```

After the first case, `--all` schedules remaining/reused E4 leaves serially, stopping on the first unfinished or nonstrict leaf. An individual later case remains selectable with `--case`. Build an E4 plan with `--e4-progress degree17_full/P9-Q8-exterior-E4-v9-progress.json`, replay it, and validate it in partial mode. Only that replayed plan can enable E3 scheduling; the scheduler requires all715 core four-sets absent. Append the E3 progress list to a new plan, replay its leaves, and validate without `--allow-partial` for complete one-kind coverage. If any case is nonstrict, it remains an explicit unproved candidate, and subsequent staged refinements need new named nodes with backward ancestry.

These commands are instructions for later controlled execution, not a record of commands run in this preparation task.
