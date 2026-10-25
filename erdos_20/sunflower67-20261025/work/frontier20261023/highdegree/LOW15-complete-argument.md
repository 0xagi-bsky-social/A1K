# The cap15 branch at cardinality68

24 October 2026. Ordinary mathematical assembly with explicit, independently
reconstructed finite predicates. This closes the Delta<=15 branch under
the named universal imports. It is ordinary proof development, not final
review, publication, a Lean theorem, or a claim about global novelty. The
higher-degree branches are not composed into a global67 statement here.

## Precise statement and upstream imports

Let F be a finite simple four-uniform family of68 members with no three
distinct members having equal pairwise intersections, including empty
core. Under H27, the recorded I8/B4/isolation results, the universal I7
catalogue and its arbitrary-support proof, the stated HP15/crowding inputs,
and Jin's graph homomorphism theorem, one cannot have Delta(F)<=15.

The finite predicates used below are stated individually and have saved
exact checks. They are not treated as Lean axioms or inferred from a
solver's floating-point status. The independent finite evidence is still
ordinary executable mathematics, not Lean kernel verification.

The acyclic upstream route is already assembled in
`LOW15-NO44-ordinary-closure.md`:

1. H27 makes each actual disjoint complement intersecting of size at
   most27, hence N(Q)>=41 for every actual member Q.
2. The cap15 cone argument excludes P10; the large-singleton triangle
   argument and its two-low-root continuation give N(Q)<=44.
3. This neighbourhood bound excludes P9 globally, giving every exact
   singleton pool size at most8.
4. The ordinary P8 argument excludes the type with omitted blocks
   intersecting in one point; only the two-cover P8 and Q8 remain.
5. The four N44 profiles force a size15 link with rho exactly7 and an
   actual triple of degree pattern(2,4,4) or(3,3,4). The universal rho7
   classification gives R16 minus one triple, which has neither pattern.
   Consequently every actual neighbourhood has size at most43.

The rho7 classification is used in that last step as an ordinary
classification on a precisely guarded domain. It does not assume the
later rho<=6 result or the later exclusion of complete R15 links.
The named note gives the full upstream hashes and boundary of the
prior cross-star imports.

The Delta<=14 branch is already excluded by
`LOW14-NO43-ordinary-closure.md`, using its ordinary N43 core proof and
Jin's graph step. Hence a hypothetical remaining F has an actual point
x of degree15. Write L=L_x for its complete fifteen-triple link.

## The complete size15 link has only three possible rho domains

Define rho(L) as the largest number of triples in L disjoint from an
actual triple of L. Every such disjoint family is an exact singleton
pool of F at the corresponding member {x} union A. The global singleton
bound therefore gives rho(L)<=8.

The exhaustive cases are rho<=6, rho=7, and rho=8. Their exclusions are
independent of an assumed finite ambient support. We now state each one
and the exact finite evidence it uses.

## Exclude rho<=6 by the proved eleven-point reduction and proof trees

The ordinary argument in `R15-rho6-degree2-support-reduction.md`, with
its independent reconstruction in `R15-degree2-independent-ordinary-check.md`,
shows that a hypothetical size15 SF3 family with rho<=6 has minimum used
degree at least3 and support at most11. The support bound is derived,
not imposed on the original family.

The low-degree reduction has two finite leaves:

* With a degree-two point and a degree-six neighbour, all possible
  identifications of three forced triads give91 normalized motifs.
  Six survive the immediate literal obstructions, and none permits
  a thirteenth triple. The independent reconstruction verifies every
  possible next triple, including arbitrary exterior points through
  three fresh normalized labels.
* With a degree-two point and no degree-six neighbour, there are78
  normalized nine-triple motifs and18 survive. Every allowed future
  triple with a new point has exactly one new point, and the sum of
  the remaining capacities at its possible old pairs is at most3.
  Thus a whole completion introduces at most three distinct new
  points. The independent check tests all74,761 six-element subsets
  of the resulting admitted next-triple lists; each has a literal
  sunflower with an actual motif member. No completion exists.

The independent receipt `R15-degree2-independent-check.json` is PASS.
Its source imports neither motif producer and reconstructs their
normalized domains, actual witnesses and every projected pair capacity.
This supplies the arbitrary-support premise for the next finite step.

For completeness, the support inequality uses I, the number of unordered
intersecting member pairs, and r(v), the number of codegree-two partners:

    I>=15*8/2=60,
    I=sum_v [binom(d(v),2)-r(v)/2], sum_v d(v)=45.

For degrees3,4,5,6 the maximum summands are5/2,5,8,12, respectively,
and each is at most19*d/6-7. Therefore60<=285/2-7n and n<=11.
Degree at most4 would give I<=225/4<60. A degree5 or6 point exists,
and its complete SF2 point-link is respectively C5 or triangle-plus-
two-edge-path, or two disjoint triangles.

Pad to eleven points and normalize that complete root star. Every
remaining triple avoids the root; all120 triples on the ten other
points are retained as the initial candidate domain. The independently
replayed proof trees exclude target15 in all three domains:

| Complete root link | Global degree cap | Nodes | Checked colour pairs | Solutions |
|---|---:|---:|---:|---:|
| Two triangles | 6 | 3657 | 101266 | 0 |
| C5 | 5 | 5109 | 170054 | 0 |
| Triangle plus two-edge path | 5 | 3455 | 113537 | 0 |

The set-based replayer reconstructs the entire candidate domain, every
scalar rejection, each pair incompatibility, every child and the omitted
colour prefix. It imports no producer search code. All three receipts
are PASS. Changed target, missing child and wrong source commitment
were also rejected by the saved negative controls. These are fresh
size15 trees; no size16 exhaustion is transferred to size15.

Thus rho<=6 is excluded under the explicit finite predicates above.

## Exclude rho=7 by two ordinary complete-link contradictions

The ordinary theorem `LOW15-R15-rho7-classification.md` says that a
fifteen-member SF3 family with rho exactly7 is R16 minus one triple.
It imports the complete arbitrary-support I7 catalogue, not a rho<=6
classification. Its two deletion types are excluded directly in F.

For an outer-triple deletion, all four hub triples remain actual cones.
Count residual traces on the four hubs by S,P,T,q. The four actual hub
anchors give3S+4P+4T+4q>=104; the hub degree budget gives
S+2P+3T+4q<=37. Hence2P+5T+8q<=7. Every residual singleton s_i is at
most8; if any p_ij>0 then s_i,s_j<=7, so S<=30. These bounds contradict
the first inequality in all cases. The full argument, including actual
anchor identities, is `LOW15-R15-outer-deletion-exclusion.md`.

For a hub-triple deletion, let the missing triple be123 and special
hub0. Put a=s0, let b_i=s_i at the other three hubs, let Y=p12+p13+p23,
and let t0 count residual trace123. Three surviving actual hub anchors
and the total hub degree budget give P+3T+5q<=a<=8. The degree budget
at0 gives

    Y+t0>=1+delta_mid+delta_max,  delta_i=8-b_i.

The complete five-edge x-star at each satellite hub is a disjoint
triangle and two-edge path with centre0. At singleton equality
b_i+p_ij=8, B4 makes its near family intersecting. A non-x near triple
must then be0 plus two points of the outer triangle. Consequently
p_ik+T-t_i+q=0; the p0i category is retained.

If t0>0, every satellite pair capacity is strict. If t0=0, the displayed
lower bound first forces all three satellite pair categories positive,
and the same guard makes their capacities strict. Therefore
Y<=2*delta_min+delta_mid-3. Combining inequalities gives

    Y>=9-3t0, whereas Y<=P<=8-3t0,

a contradiction. `LOW15-R15-hub-deletion-exclusion.md` proves all guards
and traces explicitly, including q and arbitrary exterior members.
Both ordinary complete-link arguments were separately inspected in the
parent task and reconstructed in the independent ordinary note
`LOW15-R15-hub-exclusion-independent-check.md`; neither uses a numerical
feasibility assertion.

Thus rho=7 is excluded.

## Exclude rho=8 by A3 and independently reconstructed cover bounds

The graph reduction in `LOW15-A3-star-fibre-reduction.md` now applies:
N(Q)<=43 gives minimum disjointness degree25; H27 gives independence
number at most27. Jin and the elementary fibre-mass argument force
the cyclic A3 image on eight indices.

For a degree15 star, either its image support is independent, yielding
at least10 actual full four-covers of L, or its support has four
consecutive indices and only the endpoint pair is adjacent. Each
endpoint star weight is1 or2. Deleting its actual cones gives at least
11 covers for a one-cone deletion or at least12 for a two-cone deletion.
These statements do not assume a complete graph blowup.

If rho(L)=8, choose an actual triple with exactly eight disjoint
companions H. H is intersecting, and B4 makes the other seven triples
K intersecting. By I8/I7 classification and isolation, H is P8 or Q8,
K is one of the eight I7 types, and their only possible shared points
are Q8 leaves. The P8 omission-intersection1 type was already excluded
upstream. This leaves eight separated P8-i2+I7 models and thirteen
Q8+I7 gluings.

The complete gluing domain is proved independently in
`LOW15-A3-cover-independent-bridge.md`: a shared Q8 leaf v is allowed
exactly when the I7 point-link at v is intersecting. Its allowed
vertices are none for H0,H1,H3,H4,H5; {0} for H2,H6; and {5,6} for H7.
This gives all thirteen gluings, including shared leaves, without a
support cutoff or reliance on rejected producer configurations.

The finite cover predicate is as follows. For every one of these21
literal fifteen-triple links and all121 sets of at most two deleted
triples, let C3 be its support three-covers and P4 its support
four-covers containing no C3. Then the maxima of2|C3|+|P4| at deletion
sizes0,1,2 are respectively2,4,10.

The new independent source `replay_low15_eight_seven_covers.py` checks
this predicate by deletion-first literal set tests, independently of
the earlier producer's support-first distribution. It constructs the
analytical Q8 domain directly, imports no producer and includes no
R15 models. Its2541 cases all passed in1.21 seconds. No incidence
correction is required for this selected domain.

To transfer to F, at least13 link triples remain after two deletions,
and two support points meet at most12 triples by the universal SF3
point-degree bound6. Thus every ambient four-cover uses at least three
points of the displayed support. It either contains a C3 or equals
a P4. Global triple codegree2 and simplicity bound actual covers by
2|C3|+|P4|, including every possible exterior completion and coincidence.

The A3 requirements10,11,12 exceed the corresponding bounds2,4,10.
This excludes rho=8 and exhausts the possibilities for the degree15
point x. The hypothetical cap15 family cannot exist.

## Completed finite evidence and remaining assurance boundary

All finite predicates used in the new size15 closing steps now have
independent exact reconstruction or proof-tree replay. The mathematical
statement still relies on the explicitly named universal prior inputs,
including H27, B4/isolation, I8/I7 classification, the prior HP15/crowding
scope, and Jin. This note does not independently reprove those external
inputs or claim Lean verification. It is a complete conditional ordinary
cap15 argument, rather than a pending N43 census or global theorem audit.

The N43 ordinary subcases developed elsewhere are useful independent
structure results, but the A3 proof here only needs N<=43. It therefore
does not assume that all N43 anchors have been excluded.

## Byte identities at assembly

| Source or receipt | SHA256 |
|---|---|
| LOW15-NO44-ordinary-closure.md | 3d112ee85712e5b00782c798116bccc981b43eb9818329da318eb9e7e94ebd83 |
| LOW14-NO43-ordinary-closure.md | 32ba4c4bde45e505a7bf0add66befa040cf2f9b2e2739edf9f5c87d849228cdc |
| LOW15-R15-rho7-classification.md | 151e0cde17bdf12f3ab348248a47d721edadc23baf6aee8e32aeacb0971056e6 |
| LOW15-R15-outer-deletion-exclusion.md | b665f4aa18d202df65383768d9ade1247d4feb46b7beea026e383a7e10180550 |
| LOW15-R15-hub-deletion-exclusion.md | 9fcacff3efee757a9bc0005fe61639f88e9b532b754b8cd0adbbeba5153155d3 |
| LOW15-R15-hub-exclusion-independent-check.md | 99432e42707ef712176bf6f3f410868052b7663792bfa0245ea98bcb7209d6b9 |
| R15-degree2-independent-ordinary-check.md | a097db1ab568276df356cb9d91ca0da0b43c5ba1fcf12c052716b67c77beebc6 |
| R15-degree2-independent-check.json | cf156eb974471d2deb8cbdd6e034628086e4f386f34c29f20d73b0fecd9eaf81 |
| R15-rho6-finite-closure.md | 36fe90448caf0326304c6394fd6eedc91d81ea90e8f4a81b5d0cb98348e1f8bd |
| R15-rho6-two-triangles-replay.json | ad0bf2bb36da2d92628d7538aaf99f2c39e03380f1e19e83e0601420176d6190 |
| R15-rho6-cycle5-replay.json | aa5f38af7195deed47fb008c7bd0eea8b036e2c8a24a74011a4015de40e2b87b |
| R15-rho6-triangle-path-replay.json | ef6bd7ed389c73cd16be561678d5ec277ebfc8b7a636e4d96e21cea665f900eb |
| LOW15-A3-cover-independent-bridge.md | 43a8e28c18d135437ff97f4012f3d49b7015152a538c2d02b1cb12616968c17b |
| replay_low15_eight_seven_covers.py | ebc5c607ab5f88b1427b01757e55c4567e2982af81b920cbcb0b7be120755296 |
| LOW15-eight-seven-cover-independent-replay.json | a0f011d3f75df225f386fe8c1b0c266cc199b0d0861f9d2a05d009e613821b10 |

The degree2 independent checker is
`72482f0ce7cbb4990dba7df55958c41693ae85d5d7b332c062c881181ae0accd`.
The rho6 tree replayer is
`020a9c4c6bf3ee0c22771e87fbcf0fe850e87053fd5e87a06879d4d59f99c522`.
The selected cover relation digest is
`c0416f49c5e293274a6936717e6f312a7d0df27923c88cca236d176c4439d715`.
The three tree hashes and all upstream finite identities are preserved
inside their separately bound receipts. No frozen producer, prior note,
or earlier receipt was changed by this assembly.
