# The size-68 contradiction and the resulting upper bound

24 October 2026. Ordinary computer-assisted mathematical composition. This
working proof note is separate from final specialist review and publication.
Its software evidence is not an end-to-end Lean theorem.

## Literal statement

Let F be a finite simple family of four-element sets on an arbitrary ground
set. Suppose no three distinct members A,B,C satisfy

    A intersect B = A intersect C = B intersect C.

The common intersection is allowed to be empty. Then |F| is at most67.
Equivalently, every such family of at least68 members contains a
three-sunflower. In the maximum-size convention this is M(4,3)<=67; it is
not a forcing threshold of67. With the previously known construction54,
the resulting interval is54<=M(4,3)<=67.

The claim is an ordinary computer-assisted theorem using the cited prior
theorems below and the exact finite predicates in the present proof package.
Importing a previously established theorem is ordinary mathematical practice;
it does not mean that theorem has been re-proved in this project's Lean
closure. The distinction matters for the assurance claim.

## Mathematical proof by maximum degree

If |F|>=68, retain any68 members. Uniformity, simplicity and the prohibited
configuration are hereditary, so it suffices to contradict |F|=68. All
following steps concern this single fixed subfamily; no minimum-degree
assertion is transferred from a larger family through deletion.

For an actual member R, the members disjoint from R are intersecting.
Otherwise two disjoint such members and R form an empty-core sunflower.
The prior intersecting bound H27 therefore gives |N[R]|>=68-27=41.
The universal SF3 bound20 applied to every complete point-link gives
maximum point degree Delta<=20; the corresponding pair and triple
codegree bounds are6 and2.

1. If Delta=20, choose an actual degree20 point. Its complete link has
   two disjoint P10 components. The internal-completion and exterior
   arguments in `internal-proof.md`, `stage2-proof.md` and
   `D20-proof-check.md` exclude it at the actual residual target48.
   These arguments do not use any degree18-guarded prior lemma.
   Consequently Delta<=19.
2. If Delta=19, its complete link is P10+P9. The43 active exact leaves,
   their independent literal coverage, the equality-case argument and
   the ordinary terminal separation in `D19-complete-argument.md`
   exclude the required49 residual members. Consequently Delta<=18.
3. At this point the cited mu41/cap18 cross-star, crowding, minimum-used-
   degree and R61 theorems become applicable. If Delta=18, the complete
   link is P9+P9 or P10+I8. `D18-complete-argument.md` covers both,
   including the two P8 types and Q8. All169 active finite leaves passed
   exact integer replay and their marker stages have independent literal
   coverage. The terminal residual bounds38 and37 contradict50.
   Consequently Delta<=17.
4. If Delta=17, the complete link is P10+I7 or P9+I8. The P10 alternative
   uses12 exact internal exclusions followed by the ordinary contradiction
   240<=234, independent of an enumeration of the opposite I7 support.
   The P9 alternatives have complete exact plans of131,92 and94 leaves
   for P8-i1, P8-i2 and Q8. Each has complete literal stage coverage.
   After core-four and mixed-core-three exclusion, the ordinary terminal
   bound is51<=27+13=40. The components, trace multiplicities and
   arbitrary exterior completions are handled in `D17-complete-argument.md`
   and its explicit bridges. Consequently Delta<=16.
5. If Delta=16, `D16-complete-argument.md` derives, in acyclic order,
   absence of P10, neighbourhood<=46, absence of P9, singleton<=8,
   neighbourhood<=45, absence of P8-i1, and neighbourhood<=44.
   R61 excludes R16; the remaining complete link has form I8+I8.
   The independent5576-case deletion-cover calculation, ordinary graph
   reduction and independent2188-profile/124323-star fibre reconstruction
   exclude all possibilities. Consequently Delta<=15.
6. `LOW15-complete-argument.md` first excludes Delta<=14 by its ordinary
   N43-core and graph contradiction, and hence supplies a degree15 point.
   Its complete link L has rho<=8. The new universal15-triple result
   excludes rho<=6; it has an arbitrary-support reduction and three
   independently reconstructed finite proof trees. At rho=7, the
   complete link is R16 with one triple deleted and both deletion types
   have ordinary incidence contradictions. At rho=8, the complete8+7
   classification and independent2541-case deletion-cover reconstruction
   contradict the A3 fibre requirements. The direct Jin k=3 proof in
   `LOW15-direct-Jin-A3-addon.md` gives the required A3 description
   without an empty-fibre reduction. This excludes Delta<=15.

The alternatives Delta=20,19,18,17,16 and Delta<=15 exhaust Delta<=20.
The contradiction proves the literal statement, at the ordinary
computer-assisted evidence level described here. No separate unproved
degree, singleton, neighbourhood, support or terminal hypothesis is left
in this composition. The prior global bound68 itself is not a premise.

## Prior theorem imports and their evidence boundaries

H27 is Proposition6.7 of Axante, Budala, Chitic, Dumitru and Nacu,
arXiv:2609.06175v1. Its exact family and sunflower conventions agree
with the statement above. Its unrestricted-support reduction and
canonical-augmentation proof are external computational mathematics;
this project did not replay its entire exhaustive-search ledger.

Jin's strict triangle-free graph homomorphism theorem is used for
1<=k<=9 in the form stated as Theorem A in Nikiforov, arXiv:1001.2070v1.
Every application verifies the strict threshold. The actual graph has
the68 members as vertices, not the underlying points. Its independent
sets are intersecting subfamilies and hence have size at most27.

The small-rank classifications, isolation, B4 and high-link statements
are imported from the frozen Babanskyy source and their written proofs.
The finite prior components actually needed are `terminal.r16`,
`terminal.cross15`, `terminal.crowding`, and `terminal.cap61`, all among
the six prior suites already replayed normally and with optimization.
The universal trace foundations have ordinary proofs; rooted signature
tables enumerate those classified finite models. The minimum7 finite
checks occur inside the already replayed crowding package. No old mu42
bootstrap, old size69 high-degree exclusion or old terminal fibre census
is being applied at size68. See `PRIOR_DELTA18_UNLOCK.md` and the
updated global dependency assessment for exact source scope.

The source repository is pinned to commit
90c03c79bcf44eb8f61dff1b86091b822cc4cd3c. Reuse of these particular prior
theorems does not claim a replay of all42 suites in that prior project.

## Software and formal assurance

The LP solver is a discovery device. Active certificates are exact
integer weighted inequalities with all coefficient columns and box
corrections included. A strict upper numerator or a negative zero-
objective numerator, recomputed on the bound model, supplies each
finite exclusion. Model generation is shared with the arithmetic
replayer; its ordinary family-to-model implication is a separate
written proof obligation supplied in the versioned bridge notes.

Orbit and stage coverage is checked by literal independent code. The
Q8 final94-leaf plan has no missing core-four or mixed-three trace and
uses no future/sibling absence as a premise. Three new corruption
controls reject an omitted E3 leaf, a self-dependency and a changed
replay commitment. The low-degree covers, fibres and rho-six proof
trees also have separately implemented reconstructions.

Under the SuperMath assurance vocabulary, these external exact checks
remain `certificate-diagnostic`; this label does not convert them into
Lean proofs. Several general set lemmas and five new arithmetic
interfaces are individually `axiom-audited` under the pinned Lean4.26.0
environment and the allowed axioms propext, Classical.choice and
Quot.sound. Their proved statements do not include the whole theorem
above. There is no clean-kernel replay or independent human certification
of this complete result at this save.

## Scope of the frontier comparison

The fresh24October search, cutoff07:57:31UTC, located54<=M(4,3)<=68 as
the strongest directly comparable primary claim. The present upper67
would strictly improve that located numerical upper bound, using its
local structural and computational foundations. The search found no
earlier comparable upper67 claim, but cannot certify absence from all
unindexed, inaccessible, unpublished or subsequently posted work.

The19October Bucić–He–Lee result concerns the ground-set
Erdős–Szemerédi problem. Neither this fixed-rank improvement nor its
new size15 structural lemma resolves the all-rank Erdős–Rado sunflower
conjecture. Global mathematical dominance and exhaustive originality
are not asserted.

## Primary links

- Axante et al., [arXiv:2609.06175v1](https://arxiv.org/abs/2609.06175v1).
- Babanskyy, [aiXiv2610.01292v1](https://aixiv.online/abs/2610.01292).
- Jin, [Combinatorics, Probability and Computing2(4),479–490](https://doi.org/10.1017/S0963548300000845).
- Nikiforov, [arXiv:1001.2070v1](https://arxiv.org/abs/1001.2070v1).
- Bucić, He and Lee, [arXiv:2610.26686v1](https://arxiv.org/abs/2610.26686v1).
