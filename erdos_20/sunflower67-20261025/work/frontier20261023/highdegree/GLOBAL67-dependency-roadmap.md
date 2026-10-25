# Acyclic dependency roadmap for the size-68 contradiction

24 October 2026. Ordinary proof development. This is a dependency and status
assembly, not final scholarly review, an end-to-end Lean proof, publication,
or a claim that every imported theorem has been independently proved here.
No model, solver, coefficient replay, large enumeration, or Lean job was run
to write this note. Existing sources and receipts were read and preserved.
The initial status snapshot was read at 08:35:57 UTC. The completed Q8
coverage was subsequently read and bound below in this same development task.

**Current conclusion.** Every maximum-degree case now has a completed
ordinary argument and its required new finite predicates have passed their
recorded exact checks. In particular the final94-leaf P9+Q8 chain now has
exact replay and independent complete coverage PASS. Accepting the cited
established theorems in the usual way, the acyclic composition below proves
M(4,3)<=67 as an ordinary computer-assisted result. No unresolved new
mathematical assumption or unchecked new finite predicate was identified.
A consolidated D17 exposition and global proof write-up remain packaging
work, not a further case obstruction.

H27, Jin, B4 and the cited classification theorems are mathematical inputs
with specified sources, not conjectural hypotheses. Earlier notes often
said "conditional" to expose their source dependencies; that wording must
not be confused with a still-unproved new lemma. Lack of an end-to-end Lean
proof, a separate full-code reconstruction, or final scholarly review is a
different assurance issue and does not make ordinary theorem use logically
conditional. This note does not establish priority or novelty by itself.

## 1. Exact statement, normalization, and common foundations

The intended statement concerns finite simple **exactly four-uniform**
families with no three distinct members having equal pairwise intersections,
including the empty intersection. To prove the upper bound67, it suffices
to exclude a family F of exactly68 members: every larger family contains
such a subfamily and sunflower-freeness is hereditary. This does not use
the prior reported upper bound68 as a premise.

All branches can be composed on this one fixed F. Write Delta for its
maximum used point degree and N[A] for the closed meeting neighbourhood of
an actual A in F. For any A, the members disjoint from A are intersecting,
since two disjoint such members together with A would form an empty-core
sunflower. Thus the imported H27 gives

    |N[A]| >= 68-27 = 41.

H27 also bounds the independence number of the disjointness graph by27.
The graph is triangle-free by the same empty-core prohibition.

The universal SF3 bound20 gives Delta<=20. Its proof is before the prior
size69 reduction: an actual triple has closed neighbourhood at most13;
at size at least21 its disjoint class has at least8 triples, and B4 makes
both sides intersecting, each of size at most10. The universal SF2 and
SF1 bounds similarly give pair and triple codegrees at most6 and2.
The detailed source bridge is in `D18-complete-argument.md`, using the
frozen paper's Corollary `cor:triple20`, lines333--350.

If a branch is instead applied directly to a larger family, a restriction
to68 must retain the entire selected root star: retain all d(x)<=20
members through x and choose the other68-d(x) members outside x. This
preserves the complete classified root link. Recompute mu>=41 in the
restricted family; do not inherit minimum positive degree through an
arbitrary restriction.

The common external and prior inputs have the following precise scopes.

| Input | Scope and role | Source boundary |
|---|---|---|
| H27 | Every intersecting simple SF4 family has size at most27; supplies mu41, intersecting-pool rows, terminal counts, graph independence bound. | External theorem identified by the frozen paper, lines104--110 and148--160; not re-proved locally. |
| Universal small-rank structure | SF2<=6; intersecting SF3<=10; I10=P10, I9=P9, I8=P8 or Q8; P-type whole-support isolation and Q8 core isolation with its leaves allowed to overlap; B4 near-part intersection. | Frozen paper, lines188--231 and272--350, and cited universal foundations. |
| R16 and high-link structure | Size16 with rho<=7 implies R16; its maximality supplies complete links at sizes17--20. It is not an unconditional classification of every size16 link. | Frozen paper, lines443--462 and612--636, with its imported finite package. |
| Universal I7 classification | Seven six-point types H0,...,H6 and the seven-point H7, on arbitrary support. Needed in low15 and some D17 local filters; not needed for the ordinary D17 P10 empty-interior step. | `D17-I7-classification-route.md` gives the arbitrary-support proof; `D17-i7-coverage.json` independently covers all77,520 six-point candidates, including the1,860 valid families. |
| Universal rooted trace geometry | Actual-anchor exact caps10/3/1, extension-point equalities/distinctions, rooted large-singleton signatures, margins, local43 catalogue and C5 obstruction. | Frozen `TRACE_FOUNDATIONS.md`, `local43.py`, and the source-versioned ordinary model bridges. The C5 obstruction has the ordinary replacement described below. The old mu42 bootstrap is excluded. |
| Complete C5/P5 and later local deductions | Actual complete point-link, correct support, internal-completion costs and cover capacities; marked B4, two-anchor triangle and witness-based H27 rows. | `C5-internal-compatibility.md`, `D19-singleton-I04.md`, D18/D17 versioned row notes. These deductions retain all actual-member and support guards. |
| Guarded HP15, crowding26, minimum used degree7, R61 | These require mu>=41 and Delta<=18. HP15 also requires distinct actual centres outside both actual tail supports. R61 excludes a complete R16 root link. Minimum7 is used only in the models that explicitly enable it. | `PRIOR_DELTA18_UNLOCK.md`, `prior-delta18-unlock.json`, frozen primary local arguments and selected Oct20 replay receipts. |
| Jin's graph theorem | Strict triangle-free graph homomorphism theorem in the stated range k<=9, followed by the recorded cyclic image/fibre reductions. | External theorem plus the ordinary D16 and low15 graph bridges; not locally formalized. |

The pinned primary repository is
`work/frontier20261020/prior-art68/repository`, commit
`90c03c79bcf44eb8f61dff1b86091b822cc4cd3c`.
The Oct20 `FOUNDATION_LEDGER.md` records six replayed suites, each normally
and with Python optimization, out of42 suites. The selected cross15,
crowding, cap61 and R16 outputs are reused with byte commitments. This is
neither a claim that all42 suites were checked nor a requirement to import
the entire prior size69 proof. Only the named universal/local components
above enter the present route.

There are no additional unchecked finite predicates concealed by this
input list. The following finer provenance split is useful:

* H27 is Proposition6.7 of the Axante et al. source cited by the pinned
  paper; Jin is the strict graph homomorphism theorem cited through the
  stated Theorem A. An ordinary proof may cite these established results
  without reproving them or executing a local suite.
* SF2, I8/I9/I10, isolation, B4, SF3<=20, the universal trace margins and
  extension equalities have written ordinary proofs. Rooted local signature
  coverage follows by enumerating every block subset, anchor and ordering
  of the classified models, as explained in `D19-model-bridge.md`; it is
  not an additional unexplained feasibility assertion.
* The required prior finite packages are `terminal.r16`, `terminal.cross15`,
  `terminal.crowding`, and `terminal.cap61`. All four were among the
  already completed normal and optimized selected replays. The R16 package
  covers its I7 catalogue, proof trees and structural finite predicates.
  Its wrapper's later global-use gate is not a premise of the earlier
  universal classification. The crowding package includes the rooted
  projection and private-point checks used in minimum7. These packages
  are accompanied by their written arbitrary-support reductions.
* The old `MU42.check_c5` binary certificate is unnecessary on the present
  route. `C5-internal-compatibility.md` proves the required complete-C5
  obstruction ordinarily from full R16 classification plus B4/isolation:
  R16 has no degree-five point, and every other possible sixteen-triple
  link with the complete C5 star forces an internal cycle cover. The
  full R16 package does not import that separate C5 checker, so this
  replacement introduces no cycle. Historical citations to the weaker
  C5 finite proof may be replaced by this ordinary implication.
* The two other previously replayed suites, `terminal.f69_bridge` and
  `terminal.primary`, are useful provenance checks. Their size69 numerical
  conclusions are not used to prove the fresh size68 terminal domains.
  All remaining old preliminary mu42 and size69 exclusion suites are
  outside the minimal proof path.

## 2. Global acyclic order

The sequential maximum-degree reduction is:

```text
Universal SF3 cap20 and H27 -> Delta<=20 and mu>=41
    D20 exclusion          -> Delta<=19
    D19 exclusion          -> Delta<=18
    guarded prior package becomes available here
    D18 exclusion          -> Delta<=17
    D17 P10 and P9+I8       -> Delta<=16
    D16 exclusion          -> Delta<=15
    LOW15 exclusion        -> contradiction.
```

The case theorems below Delta18 may be proved in parallel under their
explicit degree-cap hypotheses. Their use in the displayed global chain
only occurs when that cap has been established. In particular, D16 and
LOW15 do not need a completed D17 proof to be valid **conditional case
theorems**. D20 and D19 do not use HP15, crowding26, minimum7, R61, or a
support cutoff from the guarded Delta18 package.

For complete links, the structural possibilities are exhaustive:

| Degree case | Complete-link split or closing route | Current state |
|---|---|---|
| 20 | P10+P10 | Closed under the common universal imports. |
| 19 | P10+P9 | Closed under the common universal imports. |
| 18 | P9+P9, or P10+P8-i1/P8-i2/Q8 | Closed, all169 active finite leaves exactly replayed. |
| 17, contains P10 | P10+arbitrary I7 | Closed by12 internal leaves and an ordinary empty-interior contradiction. |
| 17, contains P9 | P9+P8-i1, P9+P8-i2, P9+Q8 | All closed by131,92,94 exact leaves with complete independent stage coverage. |
| 16 | R16 excluded by R61; remaining link is I8+I8 after the cap16 local reductions. | Closed with independent cover and fibre reconstruction. |
| <=15 | First exclude <=14, then a degree15 root has rho<=6, rho7, or rho8. | All three domains closed in the LOW15 assembly. |

Here rho is the largest number of complete-link triples disjoint from an
actual link triple. Isolation and high-link classification are applied to
actual complete root links, not to guessed sublinks. No ambient support
bound is silently part of this table.

## 3. Completed branches and their minimal active evidence

**D20.** `internal-proof.md` retains the internal-completion cost in the
universal C5 inequality and excludes any internal member through its new
finite coefficient cover. The marker coefficient minimum gives5r+3<=241,
hence r<=47 instead of the required48. `stage2-proof.md` then uses six
exterior marker certificates with strict residual bounds below48. Their
685 literal marker domain and arbitrary exterior multiplicities are
checked in `D20-proof-check.md`; `stage2-check.json` is PASS. Mixed-pair
removal and the H27 count12r<=20*27 give the ordinary terminal contradiction.
The identified citation precision issue is supplied by the universal
`lem:r16maximal` for degree18 in the internal lemma; it is not a missing
mu assumption. The old numerical D20 bounds that exceeded48 are inactive.

**D19.** `D19-complete-argument.md` uses43 active exact leaves and independent
literal coverage. P9 internal assignments are removed before P10 internal
assignments and the staged exterior markers. The non-strict singleton
bound49 is resolved by `Ysingle-equality-proof.md` and `doubled-P10.md`,
not by rounding. The weaker v3 phase-one family-to-model implication is
explicit in `D19-model-bridge.md`; it is not represented as the v4 model.
The terminal49-member residual is intersecting, contradicting H27.
`degree19/complete-replay-index.json` reports `ALL_43_PASS`, and
`degree19/coverage-check.json` reports PASS.

**D18.** `D18-complete-argument.md` supplies all versioned row premises and
the exact model interface. Its169 leaves are12 P10 internal assignments,
34 P9+P9 cases, and123 P10+I8 markers. The complete index binds the active
manifest and all receipts; both marker chains have independent literal
orbit/stage coverage. After those stages, the ordinary residual bounds
are38 for P9+P9 and37 for P10+I8, both below50. Q8 is used with one-point
avoidance only; it is never assigned transversal number3. Earlier equality
or pattern branches replaced by the active strict chain are unnecessary.

**D17 with P10.** The minimal route is `D17-P10-ordinary-closure.md` plus
`D17-P10-internals.md` and the12 exact component replays in
`degree17-replay/P10-nonempty-summary.json` (`all_pass=true`). The empty
internal assignment is excluded ordinarily: residual Y-incidence at most60,
P<=18 and P+E>=24 force E>=6; the ten-cone average is at least240 but at
most234. This proof treats the opposite I7 on arbitrary support. Therefore
the old H0,...,H7 full-model exterior chains, the H7 equality extension,
and their many extra receipts need not be ancestors of the global theorem.
Their historical open status does not leave a gap in this shorter route.

**D17 with P9+P8.** The explicit replayed coverage files for P8-i1 and
P8-i2 contain131 and92 active leaves, respectively. Both say
`PASS_D17_EXPLICIT_STAGE_COVERAGE_EXACT_BOUND`, complete coverage true,
inputs unchanged, and zero missing core-four or mixed-three traces.
Their ordinary terminal result is r<=40<51. The loose P9 transversal
capacity13 suffices, so no new sharp equality argument is needed here.

**D16.** `D16-complete-argument.md` records the acyclic local chain
noP10 -> N<=46 -> noP9 -> singleton<=8 -> N<=45 -> noP8-i1 -> N<=44.
R61 excludes a complete R16 link. B4 and isolation give I8+I8, with shared
Q8 leaves retained. The independent5576-case cover reconstruction verifies
deletion capacities(1,2,4,10), including all six raw12 corrections. The
new fibre reconstruction checks2188 complete profiles and124323
nonindependent star vectors over A3,...,A6; all four driver receipts are
PASS with no unresolved vector. Independent star support is excluded by
the ordinary full-cover bound. This is a fresh cardinality68 argument,
not a transfer of the old size69 fibre conclusion.

**LOW15.** `LOW15-complete-argument.md` gives the full dependency list and
byte identities. Its upstream NO44 result gives N<=43 at cap15; LOW14
supplies a degree15 point. Every exact singleton is at most8, so its
complete link has rho<=8. The rho<=6 branch uses the arbitrary-support
degree-two reduction and three independently replayed eleven-point proof
trees (12221 nodes,384857 checked colour pairs). The rho7 classification
is R16 minus one triple, and both deletion types are excluded by ordinary
incidence arguments. For rho8, Jin forces the A3 fibre regime; the complete
8+7 geometry has eight P8-i2 models and thirteen safe Q8 gluings. The
independent2541-case cover reconstruction gives(2,4,10), contradicting
the A3 requirements10,11,12. The additive
`LOW15-direct-Jin-A3-addon.md` obtains A3 directly from
25*11>4*68 and proves every fibre nonempty by the cyclic mass identity,
removing the need for an empty-fibre reduction in this branch. The new
`LOW15-assembly-independent-composition-check.md` finds no substantive gap
and checks all15 hashes in the frozen cap15 assembly. No unfinished N43 profile census, universal
NO43 result, or stronger all-degree R15 classification is an ancestor.

## 4. The completed D17 P9+Q8 chain

The current literal supports are Y={0,...,5}, Z={6,...,12}, with root15
and the canonical actual exterior marker13. The automorphism product has
order144. There are4 IY orbits on15 sets,8 IZ orbits on35 sets,58 E4 orbits
on665 sets, and24 E3 orbits on231 mixed triples. These counts are justified
by the independent literal geometry checker, not by progress counters.

`degree17_full/P9-Q8-E4-complete-plan-v9.json` is an explicit backwards-only
dependency plan. Its matching coverage file binds70 exact leaves and
establishes absence of **all715 core four-sets**. In particular the former
E4_56 and E4_57 obstacles now have exact-negative phase-one replays PASS,
with numerators -406255021 and -3584828830 at scale10^10. They are sibling
stage1 nodes using the already established68-leaf antecedent; neither
assumes the other's exclusion. There is no remaining E4 equality case.

The E4 coverage result is intentionally
`PASS_D17_PARTIAL_STAGE_FACTS_ONLY`: complete_kind_coverage=false,
missing_core_four=0, missing_mixed_core_three=231, terminal applicable=false.
An E4-complete filename must not be interpreted as whole-kind completion.

`degree17_full/P9-Q8-exterior-E3-v9-progress.json` records completed24/24
and all_completed_strict=true under that bound E4 antecedent. Its assurance
correctly says discovery diagnostics only. Active leaves14--17 and20--23
are negative phase-one certificates; the other16 are strict trace-upper
certificates. Original status2 records are retained as the bound inputs
to phase one, not treated as infeasibility proofs on their own. No E3
exact-replay files were present at the initial 08:35 snapshot. This was a
temporary execution boundary, now discharged by the following later result.

The finite obligations and their now-completed resolution are precisely:

1. The24 active E3 receipts, including the eight phase-one originals and
   producer identities, are bound in
   `degree17_full/P9-Q8-complete-plan-v9.json`, extending the existing
   70-leaf E4 plan. All94 leaves have exact replay PASS.
2. `degree17_full/P9-Q8-complete-coverage-v9.json` reports
   `PASS_D17_EXPLICIT_STAGE_COVERAGE_EXACT_BOUND`, exact_leaf_count94,
   complete_kind_coverage=true, all_inputs_unchanged=true, no missing
   core-four or mixed-three trace, no unproved candidate, and terminal
   applicable=true. The explicit antecedent plan is acyclic; a future or
   sibling absence is not used as its own premise.
3. The already written ordinary terminal lemma applies. Every surviving
   trace then has size<=2 or is a pure triple on one component. P9 avoids
   every pair, Q8 avoids every singleton, so every disjoint residual pair
   has a pure-Y-transversal member. Remove those members: the remaining
   family is intersecting. Nine P9 blocks allow one completion each; its
   omitted block and complementary triple allow two each. Hence
   r<=27+13=40<51. No additional terminal geometry is pending.

These steps use `D17-generic-stage-plan.md`,
`D17-Q8-explicit-stage-development.md`, the versioned full-model bridge and
row additions, and `check_d17_stage_plan_v9.py`. The later v7--v9 copied-tail
and complement rows use the guarded mu41/cap18 HP15 theorem. They do not
use the cap16 global noP9 conclusion, which would be invalid in D17.
The two separate copied H+B and H+C families are never combined into a
claimed intersecting family containing both complementary exceptions.

The short D17 composition therefore has329 active finite leaves:
12+131+92+94, all accounted for by their named completed replay/coverage
records, followed by the ordinary P10 and P9 terminal arguments.

## 5. What remains beyond Q8, and what does not

The complete Q8 chain removes the last outstanding new mathematical case.
To make the global inference explicit, suppose a size68 F exists. The
universal cap gives Delta<=20; apply the degree20,19,18,17 and16 exclusions
successively to get Delta<=15. The LOW15 theorem contradicts that remaining
possibility. Thus no such F exists. Hereditary restriction excludes every
larger family as well, proving M(4,3)<=67.

This is a full ordinary mathematical inference with cited theorems and
exact finite certificates. A consolidated D17/global document remains
useful exposition, but its absence does not conceal a new case or lemma.
The assemblies examined here reveal no further unhandled maximum degree,
root-link geometry, low-degree profile, or new unchecked finite predicate.

This conclusion has several precise limits:

* H27, Jin, the universal structural classifications and the guarded prior
  local theorems are ordinary cited results. The theorem above uses them
  as theorems, not as unresolved conjectures. Their original proofs are
  not made locally authored or Lean-verified by being cited here.
* Exact replay of a producer-rebuilt LP is arithmetic verification of the
  supplied necessary model. The ordinary family-to-model proof and the
  independent literal orbit/stage coverage remain separate obligations.
  The existing bridge notes supply the former and complete stage coverage
  supplies the latter. This inspection did not independently rederive
  every coefficient of every frozen producer; it identified no missing
  mathematical bridge. The arithmetic implementation's shared-builder
  trust boundary is explicitly retained.
* The new independent cover reconstructions and rho6 proof-tree replays
  provide stronger algorithmic redundancy for their finite predicates.
  They remain external executable mathematics, not Lean kernel proofs.
* Generic `TerminalSeparation.lean` and `TerminalAsymmetric.lean` cover
  arbitrary ground types with H27 supplied explicitly. They do not prove
  the concrete classifications, projections, or the whole global theorem.
* The old mu42 preliminary exclusions, the prior reported global68 theorem,
  the full old42-suite chain, and a support23 cutoff are not prerequisites
  of the present global composition. The exact selected imports are the
  smaller list in section1. Replaying the unused suites would not fill
  an additional obligation in the now-completed D17 chain.

Historical statements such as "lower degree cases remain", "replay pending",
or "only degrees15 and17 remain" in immutable earlier notes are read at
their dates. The later named receipts and LOW15 assembly supersede those
status statements without changing the frozen mathematical sources.
No final-review or publication action is initiated by this roadmap.

## 6. Principal byte identities at this read

These are snapshot identities, not a new automated transitive dependency
audit. Each named complete index retains its individual receipt identities.

| File, relative to this directory | SHA256 |
|---|---|
| D20-proof-check.md | 1c852bf2dbfe8e9659702b04156d444247a7c47aea252102151e27b0b6a78580 |
| internal-proof.md | 8140e8c40c798c6d81b898960b61efb520bc1f652c27c6f6f08dee53ced08524 |
| stage2-proof.md | 69d8312479e8834d77f053a3c608d8c7f0978b2b37269fce10fddf2821a2014e |
| stage2-check.json | 25617f9b21cfdb5c8b68796a7767e6e89380a089476dbb21154e51c725596af1 |
| D19-complete-argument.md | 3592b645fc12ef44ee927473f25a75844b4f4d32133a1729abd2e731ad8e34a2 |
| degree19/complete-replay-index.json | d181dcb2d35629c2e013cf29ab85288419fc1068513554733a84a3403c739ae4 |
| degree19/coverage-check.json | 86e302db89332cd07e863527d320c8074e76e8716cb0f08a1502f851579d7461 |
| D18-complete-argument.md | 90b02358d14f58513161a7d9199dfe39668fc58a0cd2b3a33d74984a0ed5497d |
| degree18-replay/P10-nonempty-summary.json | 6c98453d107d938ae0d8d6dbaabbb5f0618746759d2957df26154458c52e23bc |
| degree18_r99/complete-replay-index.json | ab4bb0340bba145f04d14535d4a2bad2962f99ec806952c59684504258037817 |
| D18-P10-active-manifest.json | 41a906f71782390491b7e4ee001f5f97541703f593bad4403b4be2f10d9578df |
| D18-P10-coverage-diagnostic.json | 8d5db0dc63c0aa00b4bf64b5fe52c02e326725b855dd7beaeb1d0dccca1b94a3 |
| degree18_p10/complete-replay-index.json | 5cc0e7c024a20d4b53c1720efb07f8384386d2305bb8893493d6b5dd1fbf65a8 |
| D17-P10-ordinary-closure.md | a7e81d41fb75220e9b0968a699a7ebf5fcdf8ff41232ad9e88df40b4962d2855 |
| degree17-replay/P10-nonempty-summary.json | d130fb5c8f164e4ab6a164e60bd1c2e8f41021da82f48195255a3cc11690711c |
| degree17_full/P9-P8-i1-v6-replayed-coverage.json | ece6604d1df385868c5e64090cd4937e6dd31e0c37c4f68b3e9991e19820a0ad |
| degree17_full/P9-P8-i2-v6-replayed-coverage.json | c196e77fd37a1a847194267f4e9bb246b8c5795e44fe481d1df8945679b3111a |
| degree17_full/P9-Q8-E4-complete-plan-v9.json | a57524270adb7b3e983f118ab050902fcc683057dd1b058df273a95da5c7347b |
| degree17_full/P9-Q8-E4-complete-coverage-v9.json | b01f09838a5b50cdff041fde5e8fb2b4d2d4aeccadeaf3a6690cc728e70ba205 |
| degree17_full/P9-Q8-exterior-E3-v9-progress.json | 6549864275dafb5bc95c66b0c60eb5ed3ecaa8792a690028ac5ae56e99e0e0f7 |
| degree17_full/P9-Q8-complete-plan-v9.json | b2a30c54e4a8f72c3fb161274159a3c3deadd073ef2d72415f5cad9924ebf156 |
| degree17_full/P9-Q8-complete-coverage-v9.json | 81d019a295700f3a9b144732d05720adf95e040368483f1a9c06b0f74c4d6c31 |
| D16-complete-argument.md | 5628ed14a7a7a24013087de1f630f15ec2fe07479ad6dadc91d2619a0e758890 |
| D16-I8-cover-independent-replay.json | 0d2a2adc503b3ad1bd9a05dba60e98a4930672dae9b3205f5ed1b2f47f9226f4 |
| D16-fibre-k3-independent.json | 8de5b582472e36c6e34594a36f623fcd15aee7279cb8dd445da5b15b2f9f221c |
| D16-fibre-k4-independent.json | 5d8393a4c9af2276c2d7293c1a2e2240e29e548506532a671c7b8f769295d4c7 |
| D16-fibre-k5-independent.json | 7cb12abf78cc2043547012167ff5bee1f65f8f0f4b1fbb195b0c17ca7f3584e8 |
| D16-fibre-k6-independent.json | f304317a48a86837aabab7f16c2b77f61b0af9593a52147def949ec3a2014784 |
| LOW15-complete-argument.md | 6c3438b2ae2f8438b3c761019e3d1e711d13cf92679c082a7f33c8a762167b68 |
| LOW15-direct-Jin-A3-addon.md | 1ad9d57a72093d5e153b5bc0624e0068d70960a79a3c2c66ddbb3acc30fa7252 |
| LOW15-assembly-independent-composition-check.md | 1e279321a6b0eecbcc6f181d71ec9b7ab908a1e1ad0c0a14617ba9f38ab39848 |
| PRIOR_DELTA18_UNLOCK.md | 25b65f695264ae0dbcd5d97b8e66eac421cccbb9970eaf20cc8692886f855b89 |
