# Degree17 at size68: source-safe starting domain and component cuts

23 October 2026. Substantive research, not a final review or Lean proof. No solver, Lean job, or enumeration was run for this note. The D17 branch is conditional on finishing the preceding degree18 exclusion and thus establishing global Δ≤17. We work with a finite simple SF4 family F of size68, including the prohibition of empty-core sunflowers. H27 gives μ≥41. A degree17 centre leaves51 residual members.

The most economical starting point is a single-component projection: a P10 component with seven unspecified disjoint opposite triples, or a P9 component with eight. This avoids any classification of an arbitrary I7. The old D17 finite exclusions at μ42 are not imported.

## 1. The high-link alternatives and their precise scope

The universal size17 link decomposition in the pinned paper gives, on disjoint supports,

    L_x=P10(Y)⊔I7(Z),  or  P9(Y)⊔I8(Z),

where I7 is an arbitrary intersecting SF3 family of seven triples, while I8 is P8 or Q8 by the intersecting size8 classification. The latter branch therefore has a six-point P9 component and an opposite P8 on six points or Q8 on seven points. The former has a six-point P10 component, but no unproved list or support size is assigned to I7.

A central anchor x∪T in the P10 component has exact singleton count7 at x; in the P9 component that count is8. This change matters: replacing root18 by root17 in a previous domain changes whether B4 applies at the centre. No D18 catalogue is reused merely by changing a degree label.

## 2. Prior μ41 results now have their guards satisfied

The relevant earlier record is `../../frontier20261020/prior-art68/FOUNDATION_LEDGER.md`, together with `analysis/mu41/mu41-analysis.md`. The source is pinned to commit

    90c03c79bcf44eb8f61dff1b86091b822cc4cd3c.

The selected receipt `replay-selected-20261020/RECEIPT.json` records normal and optimized successful executions of terminal.cross15, terminal.crowding, terminal.cap61 and terminal.r16 on20 October. The input manifest SHA-256 is

    ecc54817e8e81242a59ef6b033e74e472d3ffbb3e80f9f0d9f0e8264acf40b18.

These unchanged successful jobs were not rerun here. They are a selected-four-suite partial replay, not a replay of all42 suites, independent human validation, a proof of H27/Jin, or an end-to-end Lean proof.

The source crowding theorem has guards μ≥41 and Δ≤18, already implied in this conditional D17 branch. It bounds the three largest exact singleton counts at every actual anchor by26. The ledger's written rooted-signature/private-vertex bridge gives minimum used degree7 and, at cardinality68, support at most23. These are existing prior results; no originality claim is made for them. They are not the old μ42 minimum4 or star-charge argument.

Useful valid scalar rows are therefore:

    7≤d(v)≤17,
    d(u)+d(v)≥19 for co-occurring points,
    Σ_(v∈R)d(v)≥50 for every actual member R,
    2d(v)+Σ_(w∈R∖{v})d(w)≥59 for each v∈R,
    sum of any three exact singleton counts≤26.

The asymmetric degree inequality follows from the crowding proof: writing m=d(v), the sum of the other three degrees is at least59−2m. It does not require v to be the minimum-degree point. The support interval at size68 is16≤|supp F|≤23, since 272/17=16; using a single-component projection does not require imposing any finite exterior universe.

## 3. Use the existing cross-star bound, not the weaker HP16

The prior paper `paper/main.tex:1001–1015` states a cross-star theorem with explicit guards: distinct centres a,b avoid both tail supports; both tail families are intersecting SF3; they are cross-intersecting; all lifted four-sets are actual members of the same F. If the two tail sizes sum to at least16, an actual member R satisfies

    |N[R]|≤d(a)+d(b)−d(a,b)+4.

Under Δ≤17 the right side is at most38, contradicting μ≥41. Under the original guard Δ≤18 it is at most40, already a contradiction. This theorem uses the finite433-case cross16 certificate and its arbitrary-support reduction, not a bare finite-support experiment. Its source certificate/checker are `companion/terminal/cross15/results/cross16_certificate.json` and `companion/terminal/cross15/src/verify.py` and are among the selected replayed suites.

For the complete exterior pools H_y at distinct points of the same P10 or P9 component, all guards hold: the centres are component points, all tails avoid the component and x, and a central block avoiding the two points proves cross-intersection. Therefore

    h_y+h_z≤15.                                            (HP15)

This is stronger than the HP16 and near-P10 consequences written earlier in this continuation. Those simpler ordinary arguments remain useful explanations of special configurations, but they must not be presented as stronger or novel substitutes for this prior theorem. At d≤17, PP34 is tautological; the selector consequences below are more useful.

All previously justified pool rows still apply: total pool P≤27, P≤22 if one pool has size9, P≤20 if one has size10, the affine2P+7h_y≤110, and the conditional selector penalty5 at singleton9 /7 at singleton10. Whole-pool identification uses the actual shared pool across every central anchor, including the Q8 leaf caveat at singleton8.

## 4. A compact high-degree selector reduction

Call a neighbour of a P10/P9 component high when its complete central point-link is C5 and its global degree is at least16, or when it is P5 and its degree is at least17. Under μ41 and Δ≤18,

    at most one neighbour in that component is high.         (ONE-HIGH)

This is a corollary of the imported cross-star bound and ordinary complete-star compatibility. It is not asserted as a new priority result. The proof below avoids a new finite classification.

### Five covers and two incompatibilities

At a high C5 point y, complete-C5 separation gives an intersecting near part consisting of its five central cones and all I_y internal members. Every internal residual is a three-point cover of the C5. There are exactly five possible covers, so

    I_y≤5,   h_y=d(y)−5−I_y.

For two points u,v of a P10 completion, exactly two of the five internal C5 covers at u contain v and fail to cover the complete C5 at v. This can be checked in one canonical labelling without enumerating an internal family. Set u=0,v=1 in

    P10={012,015,023,034,045,124,134,135,235,245}.

The five internal four-sets compatible with the complete C5 at0 are

    0245,0235,0135,0134,0124.

Of these,0135 is a noncover at1 because it misses point1's edge24;0124 is a noncover at1 because it misses edge35. A cyclic relabelling of the point0 C5 places any other point at1, and any chosen point can first be labelled0 by identifying its C5. The five non-star triples of a P10 are exactly that C5's five covers, so this relabelling respects the whole P10. The statement applies to full C5 points of a P9 as well, since its deleted block avoids such points.

### C5 with C5

If u,v are both high C5 points, the two incompatible internal members at each point are absent. Thus I_u,I_v≤3 and h_u,h_v≥16−5−3=8. This contradicts HP15.

### P5 with P5

At a P5 point with degree17 or18, high-link separation gives an exterior part of size at least8. Indeed its near part has at least7 members and cannot be P10, since x has complete point-degree4 there. A near Q8 is also impossible because its degree4 point-link is C4 rather than P5. The near size is therefore7,8 or9, with far size at least8. Two high P5 points would again contradict HP15.

### P5 with C5

Suppose y is high P5 and z is high C5. If y's near part has size8 or9, it is P8/P9 on the six points of the complete path star. Completing the path to its C5 adds its endpoint edge, giving the original P10 completion. Such a near part contains at least four of its five non-star internal C5 covers. Two of those are noncovers at the high C5 point z and would have to be absent, a contradiction.

Hence y's near part has size7. Under Δ≤18 and the high-link classification, its far part must then have size10 and d(y)=17. At z, I_z≤5 gives h_z≥16−5−5=6. Their total is at least16, contradicting HP15. This proves ONE-HIGH in all cases.

At cap17 the immediate selector rows are

    P10: Σ_(y∈Y)[d(y)≥16]≤1,
    P9:  Σ_(P5 y)[d(y)=17]+Σ_(C5 y)[d(y)≥16]≤1.

They imply the weaker aggregate component degree bounds

    Σ_(y∈P10)d(y)≤92,
    Σ_(y∈P9)d(y)≤95.

The actual degree selectors are the preferred implementation: the aggregate bounds discard information. In particular two P5 neighbours of degree17 are impossible, giving d(u)+d(v)≤33 at cap17, and two C5 neighbours cannot both have degree16.

## 5. Smallest safe projection and what changes from the old D17 proof

Use41 nonempty component trace counts: six singleton, fifteen pair and twenty triple counts. Assign the entire internal four-set family, with presences and absences; retain the existing universal compatibility catalogues only as source dependencies. The P10 catalogue has13 orbits and the P9 catalogue79, independent of μ. Their old μ42 refutation certificates are not part of the new proof.

Use an actual centre of degree17, exact centre singleton7 on the P10 side or8 on the P9 side, global cap17, μ41, the prior minimum7/crowding package, and HP15. Keep r9=r10=0 in the general local-signature constructor unless a new argument establishes a positive near-part lower bound. Preserve the universal signature and equality/distinction rules and exact shared pair/triple margins. Add the refined P5 cover/deletion and complete-C5 rows already proved in this continuation, the whole-pool coupling, pair/singleton resource table, and ONE-HIGH through shared degree selectors.

On a P10 anchor, if e is the residual triple count, w the three residual pair counts and s the three neighbour singleton counts, the actual neighbourhood inequality is

    17+e+Σw+Σs≥41,
    e+Σw+Σs≥24.

The historical bridge used the stronger right side25, together with R42.7/N42.7 to rule out singleton9/10. Neither the ten-row table nor its ALL15/ONE14 list follows at right side24. Even with empty internals, s9 or10 must remain until valid current constraints exclude them. Their old certificates with centre18/μ43 headers cannot be imported by label substitution.

For P10+I7, this single-component construction needs only that the other seven link members avoid the six-point P10 support. Their identities and support are unnecessary for central-anchor trace equations. They contribute seven to the exact x-singleton and are disjoint from any internal marker on the P10 component. This is the most economical initial attack; it does not classify I7 or use a fictitious opposite P8.

For P9+I8, the same one-component projection has eight opposite triples. Only if it survives should the P8/Q8 opposite shape be exposed in a full projection, retaining Q8 leaves and actual marked exterior identities. The same physical exterior triples must serve all anchors; separate degree histograms cannot replace shared trace variables.

## 6. Strong terminal goals without I7 classification

Suppose a full-link argument eventually excludes four-core residual traces and mixed three-point traces. Every remaining residual trace on Y∪Z then has size≤2 or is a pure triple. A disjoint pair of residual members must have a union trace which is a transversal of each component.

A P10 or P9 side has transversal number3. Any intersecting SF3 family of seven or eight members has transversal number at least2: a common point would give an SF2 link with at least7 edges, exceeding the universal bound6. Thus the asymmetric terminal argument from `D18-pool-research.md` applies even to arbitrary I7.

For P10+I7, every disjoint residual pair includes a pure P10 triple-transversal member. These traces are exactly the ten P10 blocks, each with at most one residual completion after its central cone. Removing this class leaves an intersecting family, so

    r≤27+10=37.

For P9+I8, remove instead the pure P9 triple-transversal class. The nine prescribed blocks have one residual completion each. The missing block and its complement have at most two completions jointly: if both occur with distinct exterior points, those members and an opposite cone are disjoint. Hence

    r≤27+11=38.

Both are far below residual51. These conclusions are conditional on the stated four-core and mixed-three exclusions; those exclusions are the substantive remaining work. No hypothesis τ(I7)=3 is made, and mixed pair traces are allowed throughout.

## 7. Exact source boundary and next unresolved step

Pinned source locators relative to `../../frontier20261020/prior-art68/repository/`:

* `paper/main.tex:612–636`: complete universal size17 alternatives on disjoint supports.
* `paper/main.tex:968–1024`: crowding26 and the precise cross-star guard/resource-certificate reduction.
* `companion/upstream/D17/CURRENT_PREMISES.md`: old μ42/R42/minimum4 hypotheses and the exact historical bridge.
* `companion/upstream/D17/PROOF.md:1–126`: single-component setup and the old P10 ten-row/ALL15/ONE14 reduction; its μ42-dependent exclusions are not reused.
* `companion/upstream/D17/UNIVERSAL_EXTENSION_LEMMAS.md:85–152`: exterior pool cross-intersection and the Q8 six-core-triple caveat.
* `companion/terminal/crowding/code/verify.py`, read together with the ledger's `analysis/mu41/mu41-analysis.md`: the prior minimum7, member sums and support23 bridge.

The immediate research action is a fresh degree17/μ41 component constructor with those explicitly guarded priors, followed by exact necessary-domain certificates if available. This note supplies source-safe cuts and terminal targets, but does not claim that either high-root branch is already excluded or that the whole external theorem chain has been independently validated.

## 8. Prepared constructor; no mathematical computation executed

`degree17_component.py` is now prepared as a self-contained discovery constructor adapted from the D18 component source at SHA-256

    8300c77fb1bf46c35f0028debf91b41a6ed07b035d9d324fb1239b98cc5bc557.

It records that adaptation source, the pinned upstream commit, and hashes for local43, the prior ledger/μ41 analysis/selected receipt, the source paper, and the cross15 certificate/checker. Imported source drift fails closed. Later receipts also record the actual hashes of the ordinary bridge notes. No D18 local-row catalogue is imported: a later run will regenerate rows at degree17, with opposite singleton7 for P10 or8 for P9 and r9=r10=0. The internal catalogue procedure is unchanged and explicitly checks the expected13/79 orbit counts. These expected counts were not newly enumerated here.

The constructor includes the scalar and crowding rows above, refined P5 caps/conditional cover cost, C5 confinement, shared degree selectors and ONE-HIGH, HP15, H27 total pool, affine and conditional pool penalties, whole-pool lower bounds, and the existing pair/singleton resource table. It also includes two immediate actual-family inequalities: the41 represented residual trace counts total at most51−|I|, and each assigned internal member has at most27 disjoint members after counting the seven/eight unspecified opposite root cones. The latter requires no identities or finite support for I7.

Only a static Python AST syntax parse was performed. The constructor was not imported, and no catalogue, domain enumeration, solver, certificate replay, or Lean job was run. Thus no D17 orbit exclusion or numerical result is claimed by this preparation.
