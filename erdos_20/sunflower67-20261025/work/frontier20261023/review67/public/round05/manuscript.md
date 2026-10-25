# An upper bound for four-uniform three-sunflower-free families

## Abstract

We give an ordinary computer-assisted proof that a finite simple four-uniform family with no three-sunflower has at most 67 members. The forbidden configurations include the empty core. Thus the maximum-size parameter satisfies 54 ≤ M(4, 3) ≤ 67, improving the directly comparable upper 68 in the strongest primary preprint located by our 24 October 2026 literature search. The known lower 54 is unchanged. The proof works at neighbourhood lower bound 41 and excludes every possible maximum point degree. Its new low-degree ingredient is an arbitrary-support theorem: every sunflower-free family of fifteen triples has a member disjoint from at least seven other members. The high-degree cases use ordinary structural arguments, exact integer certificates and explicit acyclic marker coverage. The low-degree cases use deletion-cover and graph-fibre reductions with separately implemented finite reconstructions. The result imports the established intersecting bound 27, Jin's graph theorem, and specified prior structural results. It is not an end-to-end Lean proof. The general Erdős–Rado sunflower conjecture remains outside the claim.

## 1. Introduction and statement

A three-sunflower consists of three distinct sets A, B, C for which A ∩ B = A ∩ C = B ∩ C; their common intersection may be empty. A family is simple when it has no repeated member. In this manuscript all main-theorem members have exactly four elements. The ambient ground set is arbitrary; only the finite family's used support matters.

Let M(4, 3) denote the maximum number of members in such a sunflower-free family. This is the maximum-size convention, rather than the first cardinality forcing a sunflower.

**Theorem 1.** Every finite simple four-uniform family of at least 68 members contains a three-sunflower. Consequently M(4, 3) ≤ 67.

The assertion is an ordinary computer-assisted mathematical result. Its proof uses cited prior theorems in the usual mathematical sense and explicit finite predicates whose evidence is supplied in the companion. No unproved new maximum-degree, neighbourhood, singleton, support or terminal hypothesis is assumed. The distinction between theorem imports, written bridges and executable checks is maintained throughout.

The numerical improvement is specific to rank four and three petals. It does not prove a fixed-base all-rank Erdős–Rado bound, and it does not supersede the separate ground-set theorem of Bucić, He and Lee. “Strongest located comparable bound” describes the bounded source search, not a certificate of exhaustive global originality.

The earlier A1K finite-support reductions for 28-member intersecting families, including capacities 56 and 53, were formal-reduction results rather than unconditional extremal improvements. The present route instead works directly with a hypothetical 68-member family, incorporating the structural and computational foundations of the October 9 preprint.

## 2. Prior work and source scope

Axante, Budala, Chitic, Dumitru and Nacu [1, Proposition 6.7] prove that an intersecting simple four-uniform three-sunflower-free family has at most 27 members; Proposition 6.8 attains 27. We call its upper statement H27. Their unrestricted-support reduction precedes canonical augmentation. Their companion describes the large H27 computation as an exhaustive-search ledger, rather than a compact proof certificate. We have inspected the precise primary theorem and conventions but have not locally replayed that entire ledger. H27 is an imported computer-assisted theorem, not a new hypothesis or a locally kernel-proved fact. Their unrestricted-family bound is 54 ≤ M(4, 3) ≤ 83. The classical 27-member construction and resulting lower bound 54 go back to Abbott and Hanson; the exact unrestricted SF3 maximum 20 goes back to Abbott and Gardner. These historical attributions are recorded through [1, Section 6 and its references 2 and 4], rather than claimed as new results of [1] or of this manuscript.

During review, the H27 supplement's referenced provenance file was unavailable and absent from the inspected tracked repository tree. Its [README](https://github.com/bogdan27182/sunflower-paper/blob/main/artifacts/f43_upper_83/intersecting_27/README.md) describes three archive-hash checks; the inspected [top-level audit script](https://github.com/bogdan27182/sunflower-paper/blob/main/artifacts/f43_upper_83/intersecting_27/check_archived_run.sh) contains frontier-hash checks and invokes run-record verification and small controls, without explicit comparisons of the three compressed archive hashes. We did not execute that script or establish source-to-historical-run authentication. The companion preserves the exact fetched blobs and this inspection limit. This source audit was obtained during review, after the stated literature-search cutoff; it does not extend the novelty search.

Babanskyy's October 9 preprint [2] reports 54 ≤ M(4, 3) ≤ 68 with ordinary arbitrary-support arguments and 42 finite verification suites. We use its universal small-rank classifications, isolation, B4 and complete high-link structure, together with its correctly guarded cross-star, crowding, minimum-degree and R61 results. The source repository is pinned to commit 90c03c79bcf44eb8f61dff1b86091b822cc4cd3c. Its old size 69 and neighbourhood 42 exclusions are not transferred to size 68. Six prior suites were replayed normally and with Python optimization; the four finite packages required by the current route are r16, cross15, crowding and cap61, all among those six. We do not claim a complete replay of all 42 suites.

Jin's theorem [3], in the exact form of Theorem A in Nikiforov [4], states that for 1 ≤ k ≤ 9 a triangle-free graph of order n and minimum degree strictly greater than (k + 1)n/(3k + 2) is homomorphic to the Andrásfai graph A[k]. We verify strictness in every use. The exact theorem was checked through Nikiforov's primary scholarly restatement; the original publisher record was confirmed, but original full-text access was unavailable.

Bucić, He and Lee's October 19 preprint [5] establishes the ground-set Erdős–Szemerédi statement for all k ≥ 3. That problem is distinct from the present fixed-rank numerical extremum. The October 24 refresh also located their public Lean project and a Palomar registry entry. We have not performed a local build or transitive axiom audit of that project, so its reported formalization status is attributed to the accessible source records.

The search cutoff was 24 October 2026, 07:57:31 UTC. Fresh queries covered arXiv, aiXiv, ECCC, HAL, Zenodo, OSF, Preprints.org, Research Square, SSRN, viXra/rxiv, TechRxiv, MathOA and GitHub through available indexed searches and primary-record opens. Such coverage is not a native exhaustive enumeration of every archive. No comparable upper 67 primary result was located. Inaccessible pages, unindexed work, unpublished work and subsequent postings remain outside that negative observation. The query and retrieval logs are retained in the companion.

## 3. Definitions, imported structure and proof methods

Square-bracketed indices, as in L[x] and a[i], denote subscripts; N[R] retains its defined neighbourhood meaning.

Write SF[r] for a simple r-uniform family without a three-sunflower, including an empty core. For a point x let d(x) be its degree, and let L[x] = {A ∖ {x} : A ∈ F, x ∈ A} be its complete link. A point degree in L[x] is a codegree in F; it must not be confused with a global point degree. Write Δ for the maximum used-point degree. For an actual member R define the closed meeting neighbourhood N[R] = {A ∈ F : A ∩ R ≠ ∅}, and let μ = min[R ∈ F]|N[R]|. Define N[max] = max[R ∈ F]|N[R]|. Thus N[max] ≤ c means that every actual member R has |N[R]| ≤ c; it is distinct from the lower bound on μ. An N43 anchor is an actual member R with |N[R]| = 43. The graph degree at R is |F| − |N[R]|, so a universal neighbourhood upper bound controls graph minimum degree.

If two members disjoint from R were themselves disjoint, they and R would form an empty-core sunflower. Thus that disjoint subfamily is intersecting and H27 gives |N[R]| ≥ |F| − 27. For a hypothetical 68-member family, μ ≥ 41. The disjointness graph has the members of F as vertices. It is triangle-free, and every independent set is an intersecting subfamily of size at most 27.

The universal SF3 bound 20 yields Δ ≤ 20. The corresponding pair and triple codegrees are at most 6 and 2. The small-rank structure used below is explicit: intersecting SF3 families have at most 10 members; I10 is the canonical P10 on six points, I9 is P9 obtained by deleting one block, and I8 is P8 obtained by deleting two blocks or Q8. The P8 deletion types are distinguished by whether the omitted blocks intersect in one or two points. Q8 consists of h + e and k + e for the three edges e of a triad, together with the two triples hka, hkb. Its five-point core is isolated by the prior theorem, while its leaves may overlap other components where permitted.

The prior B4 lemma says that an exact singleton class of size at least 8 makes the complementary near part of the corresponding complete point-link intersecting. The R16 theorem concerns size 16 links with maximum disjoint count at most 7; it is not a classification of every size 16 link. Its maximality and the large-link theorem give the separated complete links at degrees 17–20. At degree 17 these are P10 + I7 or P9 + I8. The universal I7 classification has an ordinary arbitrary-support reduction followed by a finite six-point enumeration and one seven-point type.

The cross-star bound 15, crowding bound 26, minimum used degree 7 and complete-R16 total bound 61 are imported only after Δ ≤ 18 and μ ≥ 41 hold. The cross-star lemma also requires both distinct centres to lie outside both actual tail supports. In Q8 applications only the stated core isolation is used; no generic whole-support isolation or two-point avoidance is assumed.

The following literal conventions fix the component and trace notation. A string such as 012 denotes the triple {0, 1, 2}. On six distinct points,

P10 = {012, 015, 023, 034, 045, 124, 134, 135, 235, 245}.

P9 and P8 are its one-block and two-block deletions. For four distinct hubs K = {u, v, a, b} and disjoint triads D, E, with all ten points distinct, R16 consists of the six triples {u} ∪ P, {v} ∪ P for P a pair of D, the four triples contained in K, and the six triples {a} ∪ P, {b} ∪ P for P a pair of E. The twelve triples involving D or E are called outer triples, and the other four are hub triples. Write I[j] for any intersecting SF3 family of size j; compact names I7, I8, I9 and I10 have the same meaning.

In the complete-link decompositions of degrees 17–20, a component sum denotes disjoint supports as well as distinct triple families. This convention does not impose disjoint supports on the lower-degree I8 + I8 and I8 + I7 B4 partitions. In those cases the stated Q8 core isolation holds, while permitted leaves may be shared. A Q8 component has distinct hubs h, k, triad U, and two leaves; its core is {h, k} ∪ U.

For an actual anchor R and i ∈ R, its exact singleton class is {A ∈ F : A ∩ R = {i}}. Its size s[i; R] counts only that exact intersection, not the full point star. Exact pair classes p[i,j; R] are defined similarly. When a root point x of degree d is fixed, its residual family is {A ∈ F : x ∉ A}, of size r = 68 − d. In Section 6, for the four hubs K, the symbols s[i], p[i,j], t[i] and q count residual members with exact K-traces {i}, {i,j}, K ∖ {i} and K, respectively. Put S = Σ[i] s[i], P = Σ[i<j] p[i,j], and T = Σ[i] t[i]. Thus S + 2P + 3T + 4q is residual hub incidence; q is 0 or 1, and residual members avoiding K remain allowed. Compact expressions p12 and p0i denote p[1,2] and p[0,i]. These residual counts differ from full-family anchor counts.

The cyclic Andrásfai graph A[k] has vertex set Z/(3k − 1)Z and adjacency differences k, k + 1, …, 2k − 1 modulo 3k − 1. We also write A3 through A6 for A[3] through A[6]. In A3, all indices are modulo 8 and the differences are 3, 4, 5. Fibre sizes a[i], adjacent masses b[i] and deviations r[i] are defined at their use; r[i] is distinct from the residual cardinality r.

### 3.1 Exact trace projections

Fix an actual complete root star and a displayed finite core C. For each represented trace U of size at most 4, n[U] counts all root-avoiding members whose exact intersection with the represented points is U. Proper traces retain arbitrary multiplicities of exterior completions. Only full four-point traces are binary. For a marked mixed triple its one actual exterior point is represented; all other exterior points remain unrestricted. A represented core is not an ambient-support cutoff.

Every actual family maps to a feasible integral point of the necessary model. Local selector variables choose its actual integer signature at each anchor. The geometric family-to-model maps, offsets, degree capacities, complete-point-link filters and all versioned strengthening rows have separate written proofs. A certificate alone cannot replace this implication.

Numerical linear optimization only proposes multipliers. If Az ≤ b, Ez = f and l[j] ≤ z[j] ≤ u[j], choose nonnegative integer weights y, signed integer weights e and positive scale D. Put q = Aᵀy + Eᵀe and H = y · b + e · f. Then

D c · z ≤ H + Σ[j] max(l[j](Dc[j] − q[j]), u[j](Dc[j] − q[j])).

Every column, including every selector, is included. The replay checks this expression with exact integers and requires a strict comparison with the residual target times D. An infeasibility certificate instead bounds the zero objective by a negative number. A solver status, a rounded optimum, or equality with the target is not an exclusion.

The coefficient replay rebuilds through the frozen matching producer; this is shared-builder verification. Independent literal orbit and ancestry checking is a separate implementation. The low-degree cover, fibre and search-tree checks additionally have separately written reconstructions. Neither category is described as Lean kernel verification.

### 3.2 Complete staged coverage

Actual markers are reduced by the full automorphism group of the classified root components. Relabelling the entire unknown family to a marker representative does not assume that family is symmetric. Every absence fact propagated to later nodes is a complete orbit. A node may use only listed earlier facts; two sibling exclusions cannot assume each other. An absent four-set does not imply absence of a proper trace. Mixed-three exclusions cover every exterior completion after relabelling its actual exterior point.

The saved plans explicitly bind sources, receipts, exact replays and predecessor lists. A separate literal checker reconstructs the complete marker domains and tests the ancestry. Corruption controls reject missing coverage, a self-dependency and a changed replay commitment. These finite controls are evidence about those tested failure modes, not a proof of universal software correctness.

## 4. Excluding maximum degrees 20 through 17

It suffices to exclude exactly 68 members, by hereditary restriction. The following reductions apply to that same family. When a larger-family branch is used, any restriction retaining a designated complete star must keep all its members; minimum positive degree is recomputed and is not inherited through arbitrary deletion.

### 4.1 Degree 20

The complete link is P10 + P10. The ordinary internal-completion inequality retains the required resource cost. Its finite coefficient cover gives 5r + 3 ≤ 241 in a hypothetical internal case, hence r ≤ 47 against r = 48. With internals excluded, six exterior marker certificates have strict upper bounds below 48 and complete literal coverage. The surviving geometry yields 12r ≤ 20 · 27 by removal of the mixed-pair classes and H27, again contradicting r = 48. No degree 18-guarded result is used to establish this first step.

### 4.2 Degree 19

The complete link is P10 + P9. The active chain contains 43 exact certificates and independent literal coverage. It first removes the P9 internal cases, then the P10 internal cases and exterior markers. A singleton case attaining the relaxed value 49 is resolved by an ordinary equality argument synchronizing two P10 copies and obtaining a total bound 56. It is not rounded down. The resulting 49-member residual family is intersecting, contradicting H27. Thus Δ ≤ 18, and the guarded prior package now becomes applicable.

### 4.3 Degree 18

The complete link is P9 + P9 or P10 + I8. The active 169 leaves consist of 12 P10 internal certificates, 34 P9 + P9 certificates, and 123 P10 + I8 marker certificates. Every active leaf passed exact integer replay; the marker chains have independent literal orbit/stage coverage. The P10 + I8 cases include both P8 types and Q8, with the Q8 internal and exterior refinements ordered acyclically. The ordinary terminal residual bounds are 38 and 37, both below the required 50. Thus Δ ≤ 17.

### 4.4 Degree 17 with P10

First 12 exact nonempty internal-assignment orbits exclude every nonempty family of four-subsets inside the P10 support Y. There are 292 compatible complete assignments in 13 orbits, including the empty assignment.

For the empty case, let O, H, P, E count residual members with exact Y-trace sizes 0, 1, 2, 3. There are 51 residuals. The complete-C5 argument gives every Y-point global degree at most 15, so D = H + 2P + 3E ≤ 60 after subtracting the root-star incidence 30. The combined O + H pool is intersecting because P10 avoids every pair of points; hence P + E ≥ 24. The six C5 pair pools give 2P ≤ 36, so E ≥ 6.

Each of the ten actual P10 root cones has at least 41 meeting members, 17 of which are root cones. Summing its residual meeting counts gives W ≥ 240. A singleton, pair or triple trace meets respectively 5, 8 or at most 10 P10 blocks. Therefore

W ≤ 5H + 8P + 10E = 5D − 2(P + E) − 3E ≤ 300 − 48 − 18 = 234,

which is impossible. This argument leaves the opposite I7 support arbitrary.

### 4.5 Degree 17 with P9

The three opposite I8 types have the following complete exact plans.

| Opposite component | Internal-Y/internal-Z/mixed-four/mixed-three orbits | Exact leaves | Core four-sets | Mixed triples |
|---|---|---:|---:|---:|
| P8, omitted intersection 1 |4/9/84/34|131|495|180|
| P8, omitted intersection 2 |4/6/58/24|92|495|180|
| Q8 |4/8/58/24|94|715|231|

All three plans passed exact integer replay and complete independent literal coverage. For Q8, two final mixed-four orbits are excluded as siblings after the same 68 earlier nodes. Their exact zero-objective numerators are −406255021 and −3584828830 at scale 10^10. Neither uses the other as a premise. All 24 final mixed-three nodes use the completed 70-node four-stage plan; 16 use strict upper certificates and 8 use negative phase-one certificates. The complete Q8 plan has no missing trace.

After all core-four and mixed-three traces disappear, a residual trace is of size at most 2 or is a pure triple on one component. Any disjoint residual pair must jointly hit every root block. P9 needs at least 3 transversal points and I8 at least 2. If neither residual supplies a pure Y-triple, the pair cannot supply both counts. Hence every disjoint pair contains a pure-Y-transversal member.

Removing these members leaves an intersecting family of size at most 27. P9 has eleven transversal triples: its nine blocks, the omitted block B and its complement. Each retained block has at most one residual completion, because its root cone already consumes one unit of triple codegree 2; the other two triples allow at most two each. Thus r ≤ 27 + 9 + 2 + 2 = 40 < 51. This excludes every degree 17 point. The sharper bound 11 on certain paired exceptional completions is unnecessary here.

## 5. Degree 16 and the fifteen-triple structural theorem

### 5.1 Degree 16

The degree 16 proof first derives its hypotheses in the following acyclic order: no P10, N[max] ≤ 46, no P9, singleton counts ≤ 8, N[max] ≤ 45, no P8 of omitted-intersection 1 type, and N[max] ≤ 44. R61 excludes a complete R16 link. The remaining degree 16 link has form I8 + I8, including allowed Q8 leaf overlaps.

The disjointness graph has minimum degree 24 and independence number at most 27. Jin's strict theorem and the ordinary image reduction give the relevant A3 through A6 fibre regimes. The independent cover reconstruction checks 5576 deletion cases and gives actual four-cover capacities 1, 2, 4, 10 after deleting 0, 1, 2, 3 link triples. Six cases with a raw bound 12 are corrected by their actual pair-incidence restriction.

An independently implemented fibre calculation visits 2188 complete profiles and 124323 nonindependent degree 16-star vectors, with no unresolved vector. An independent image support is excluded by the ordinary full-cover argument. This closes exact degree 16. The finite domains and their arbitrary-support bridges are the new size 68 domains, not the prior size 69 fibre result.

### 5.2 A universal size 15 lemma

For a triple family L, let ρ(L) be the maximum number of members disjoint from an actual member of L.

**Theorem 2.** If L is a simple SF3 family of fifteen triples, then ρ(L) ≥ 7.

Assume ρ ≤ 6. Every triple meets at least 8 other triples, so the number I of unordered intersecting pairs is at least 60. The universal SF3 point-degree bound is 6. The low-degree argument excludes used degrees 1 and 2 without an ambient support cutoff.

For degree 2 with a degree 6 neighbour, the forced configuration gives 91 normalized motifs; six survive immediate literal obstructions and none admits a thirteenth triple. For degree 2 without such a neighbour, there are 78 normalized nine-triple motifs and 18 survivors. Every future triple with a new point uses exactly one new point. The sum of available old-pair capacities is at most 3; hence the entire six-triple completion introduces at most three distinct new points. This is a bound on the whole completion, not a separate allowance of three points per triple. A separately implemented checker considers all 74761 six-subsets of the admitted next triples; each contains a literal obstruction.

Thus every used point has degree at least 3. Let r(v) count its codegree-two partners. The exact incidence identity is

I = Σ[v][binom(d(v), 2) − r(v)/2],   Σ[v] d(v) = 45.

For d = 3, 4, 5, 6 the summands are at most 5/2, 5, 8, 12 and each is at most 19d/6 − 7. Hence 60 ≤ 285/2 − 7n and the support has size n ≤ 11. If every degree were at most 4, then I ≤ 225/4 < 60. Therefore a degree 5 or 6 point exists.

Choose a point of maximum degree. If a degree 6 point exists, choose one; its complete SF2 link is two triangles. Otherwise the maximum degree is 5, and the chosen complete link is C5 or a triangle plus a two-edge path. Only these latter two branches impose global degree cap 5. Pad to eleven points and normalize the complete root star. All 120 triples avoiding the root on the remaining ten points are included in the initial candidate domain. Three finite proof trees exclude target 15 with ρ ≤ 6. Their separately written literal-set replayer verifies every candidate, scalar rejection, incompatibility witness, child and omitted colour prefix.

| Root link | Global degree cap | Tree nodes | Checked colour pairs | Surviving solutions |
|---|---:|---:|---:|---:|
| Two triangles |6|3657|101266|0|
| C5 |5|5109|170054|0|
| Triangle plus two-edge path |5|3455|113537|0|

Changed-target, omitted-child and changed-source controls were rejected. The support reduction and complete finite exclusions prove Theorem 2 at the ordinary computer-assisted level. No size 16 search is being transferred to size 15. Its independent novelty beyond the specifically compared prior source is not claimed separately from the present extremal theorem.

## 6. Closing maximum degree at most 15

The ordinary cap 15 local arguments give no P10, no P9, singleton counts ≤ 8 and N[max] ≤ 43. The cap 14 argument shows that an N43 anchor must exist if Δ ≤ 14, then excludes its complete common-triangle core by B4, Q8 leaf matching and the guarded cross-star bound. Consequently a remaining family has an actual degree 15 point x. Its complete link L has ρ ≤ 8.

At ρ ≤ 6, Theorem 2 gives a contradiction. At ρ = 7, the ordinary universal classification gives R16 with one triple deleted. Both deletion types are excluded directly.

For an outer-triple deletion, let S, P, T, q be the residual trace totals on the four hubs. Four actual hub anchors and their degree budget imply

3S + 4P + 4T + 4q ≥ 104,   S + 2P + 3T + 4q ≤ 37.

Singleton bounds give S ≤ 32, improved to S ≤ 30 if P > 0. These integer inequalities are inconsistent.

For a hub-triple deletion, label the missing triple 123 and special hub 0. Put Y = p12 + p13 + p23, let t count trace 123, and let a ≤ b ≤ c be the ordered deficits 8 − s[i] at the satellite hubs. Actual-anchor and hub-incidence counts give

Y + 3t ≤ 8,   Y + t ≥ 1 + b + c.

The complete triangle-plus-path five-star and B4 imply that equality in a satellite pair capacity forces the other pair at that satellite, all relevant triple traces and the four-hub trace to vanish. The root pairs p0i remain allowed. If t > 0 the capacities are immediately strict; if t = 0 the displayed lower bound first makes all three satellite pair classes positive, and the same guard again makes them strict. Thus Y + 3 ≤ 2a + b, inconsistent with the two displayed inequalities and a ≤ b ≤ c. Five arithmetic interfaces, including both deletion contradictions and the support-count consequences of Theorem 2, have separately compiled Lean proofs with an observed axiom allow-list check. Their geometric hypotheses remain ordinary proofs.

At ρ = 8, the complete link is an intersecting 8 + 7 split. The P8-intersection 1 type was already excluded; all possibilities are eight separated P8-intersection 2 + I7 models and thirteen Q8 + I7 gluings. A shared Q8 leaf is allowed only at an I7 point with intersecting point-link. The permitted I7 vertices give precisely those thirteen gluings, retaining leaf sharing.

Since N[max] ≤ 43, the disjointness graph has minimum degree 25. Directly use Jin with k = 3: 25 · 11 = 275 > 4 · 68 = 272. In cyclic A3, let a[i] be the eight fibre sizes and b[i] = a[i + 3] + a[i + 4] + a[i + 5]. Their neighbourhood preimages are independent, so b[i] ≤ 27. With e[i] = 27 − b[i] we have Σe[i] = 12 and

a[i] = b[i] + b[i + 3] + b[i + 5] − 68 = 13 − e[i] − e[i + 3] − e[i + 5] ≥ 1.

All fibres are therefore occupied. Now b[i] ≥ 25 follows from an actual vertex in each fibre. Writing r[i] = b[i] − 25 gives r[i] ∈ {0, 1, 2}, Σr[i] = 4 and a[i] = 7 + r[i] + r[i + 3] + r[i + 5].

The degree 15 star-fibre argument requires at least 10 full four-covers if its image support is independent. In the nonindependent case only four consecutive occupied indices remain possible, with endpoint weights 1 or 2; deleting an endpoint's actual cones requires at least 11 or 12 four-covers after deleting 1 or 2 triples. This uses only nonedges forced by the homomorphism, not a complete blowup assumption.

A separate deletion-first reconstruction checks all 21 literal links and all 121 deletion sets of size at most 2, giving 2541 cases. Let C3 be their support three-covers and P4 their support four-covers containing no C3. The maxima of 2|C3| + |P4| are 2, 4, 10 at deletion sizes 0, 1, 2. At least 13 triples remain and two support points meet at most 12, so every ambient four-cover contains at least three support points. It contains a C3 or is a P4; triple codegree 2 and simplicity give the stated upper bound, including all exterior completions. The requirements 10, 11, 12 contradict 2, 4, 10. Thus ρ = 8 is impossible.

Every possible Δ ≤ 20 has now been excluded at size 68. This proves Theorem 1.

## 7. Evidence, reproducibility and limitations

The companion's global dependency roadmap records an acyclic order: universal cap 20/H27; degree 20; degree 19; activation of the cap 18-guarded prior package; degree 18; degree 17; degree 16; and cap 15. No support 23 cutoff is imposed on the high-degree projections. Historical pending statements in frozen notes are superseded by named later receipts, rather than silently rewritten.

The active degree 19, 18 and 17 chains contain 43, 169 and 329 finite leaves respectively. These counts describe branch incidences; some structural or component evidence is reused. They are not counts of independent evaluators. Degree 17 consists of 12 + 131 + 92 + 94. Every active leaf has the stated exact check. The global proof also uses the degree 20 cover/marker checks, the independent low-degree cover/fibre reconstructions and the new size 15 proof trees. Each layer retains its source, input and output commitments.

Formal evidence has a narrower scope. General set-theoretic terminal lemmas, the complementary-trace obstruction, small-trace pool lemmas and five new size 15 arithmetic roots are individually axiom-audited under the existing pinned Lean 4.26.0 dependency cache. The permitted axioms are propext, Classical.choice and Quot.sound; the new arithmetic roots use only propext and Quot.sound. No project axioms, sorry or native_decide supply those roots. The whole extremal theorem, external H27 ledger, full LP models and proof-tree predicates have not been assembled into an end-to-end Lean closure. No clean replay or independent human certification of the complete result is asserted.

The SuperMath term certificate-diagnostic is retained for external Python/C++ exact checks, even where two implementations agree. This is a formal-assurance distinction; ordinary computer-assisted proofs can use exact executable mathematics without claiming kernel verification. Shared model construction remains a material implementation dependence. The written family maps and independent coverage checks do not magically eliminate all potential software bugs.

The companion records the actual autonomous specialist reviews, completed rounds, dissent, revisions and exact manuscript approvals. Publication requires twelve distinct specialist contexts completing at least ten rounds and separate final Chief, Alpha and Beta audits of the same bytes. Separate agent contexts do not establish organizational independence or human certification. Review counts and acceptance are evidenced by that record, not inferred from this paragraph. A substantive defect discovered during review suspends the completion claim until repaired.

## 8. Conclusion

The assembled ordinary computer-assisted argument excludes 68-member SF4 families and yields 54 ≤ M(4, 3) ≤ 67, relative to the explicitly cited established foundations. Its main new structural component is the universal fifteen-triple disjointness lemma, together with the degree 15 deletion/fibre closure and strengthened high-degree reductions at μ 41. The numerical theorem improves the strongest directly comparable primary bound located in the fresh search. Its scope is finite rank four; broader sunflower conjectures and end-to-end formal verification remain separate problems.

## References

[1] E. Axante, C. Budala, D. Chitic, B. Dumitru and M. Nacu. *Sunflower-Free Uniform Families: Recursive Constructions and Explicit Bounds*. arXiv:2609.06175v1, 5 September 2026. Proposition 6.7 (intersecting upper 27), Proposition 6.8 and Theorem 6.9. [arXiv primary record](https://arxiv.org/abs/2609.06175v1)

[2] Oleksiy Babanskyy. *An upper bound for three-sunflower-free families of four-element sets*. aiXiv 2610.01292v1, 9 October 2026. [aiXiv primary record](https://aixiv.online/abs/2610.01292). Companion: [source repository](https://github.com/aconsciousfractal/Four-Uniform-Three-Sunflower-Bound), pinned commit 90c03c79bcf44eb8f61dff1b86091b822cc4cd3c.

[3] Guoping Jin. *Triangle-Free Graphs with High Minimal Degrees*. Combinatorics, Probability and Computing 2(4), 479–490, 1993. [publisher record](https://doi.org/10.1017/S0963548300000845)

[4] Vladimir Nikiforov. *Chromatic number and mimimum degree of K[r]-free graphs* (arXiv title spelling). arXiv:1001.2070v1, Theorem A. [arXiv primary record](https://arxiv.org/abs/1001.2070v1)

[5] Matija Bucić, Fankang He and Hyunwoo Lee. *Proof of the Erdős–Szemerédi sunflower conjecture*. arXiv:2610.26686v1, 19 October 2026. [arXiv primary record](https://arxiv.org/abs/2610.26686v1)

## Companion proof and evidence map

The review snapshot binds the exact local paths and hashes. The principal proof documents are GLOBAL67-ordinary-theorem.md; GLOBAL67-dependency-roadmap.md; D20-proof-check.md with internal-proof.md and stage2-proof.md; D19-complete-argument.md; D18-complete-argument.md; D17-complete-argument.md; D16-complete-argument.md; LOW15-complete-argument.md; LOW15-direct-Jin-A3-addon.md; and EXTERNAL-H27-JIN-SCOPE.md with its superseding EXTERNAL-H27-SCOPE-ADDENDUM-20261024.md. Each branch note specifies its source-versioned mathematical bridges and exact active receipt indices. The size 15 support reduction, independent reconstruction, tree replayer and cover bridge are separately identified in the cap 15 assembly. The supplied manifests and original tool records are local integrity evidence, not authenticated external certificates.


The following map makes the main low-degree obligations explicit. Filenames refer to `work/frontier20261023/highdegree/`; the review snapshot binds their principal assembly files and the detailed map `review67/editing/definitions-and-map.md`. Each listed receipt remains external exact evidence, with its ordinary geometric bridge, rather than a Lean kernel proof.

| Obligation | Written bridge and finite evidence | Conclusion |
|---|---|---|
| Theorem 2: used degree at least 3 | `R15-degree2-independent-ordinary-check.md`, “Ordinary motifs” and “The whole-completion exterior bound”; `recheck_R15_degree2_support.py` and `R15-degree2-independent-check.json` | Arbitrary-support normalization; 91 and 78 motifs; at most three new points across the whole completion; all 74,761 candidate six-subsets excluded. |
| Theorem 2: support and root cases | Same ordinary check, “Eleven-point support and complete root cases”; `R15-rho6-degree2-support-reduction.md`, “Consequent support reduction” | Derived support at most 11 and an actual degree 5 or 6 point, giving the three root-star types. |
| Theorem 2: complete finite exhaustion | `R15-rho6-finite-closure.md`, “Fresh exact producer and independent replay”; `replay_r15_rho6_tree.py` and the three named tree/replay receipts; completion in `R15-rho6-completed-evidence.md` | All target-15 trees checked on the derived domain; ordinary universal conclusion ρ ≥ 7. |
| Exact ρ = 7 | `LOW15-R15-rho7-classification.md`, elimination of H0–H7 and the one/two uv-triple cases | Ordinary R16-minus-one classification using the explicitly imported I7 catalogue. |
| Both R16 deletions | `LOW15-R15-outer-deletion-exclusion.md`, actual anchors and singleton capacities; `LOW15-R15-hub-deletion-exclusion.md`, B4 guard and strict satellite capacities; `LOW15-R15-hub-exclusion-independent-check.md` | Ordinary arbitrary-support incidence contradictions; five related arithmetic interfaces separately axiom-audited. |
| Degree 16 covers | `D16-I8-deletion-cover-reconstruction.md`, model completeness, arbitrary exterior transfer and raw-12 correction; `D16-I8-cover-independent-replay.json` | All 5,576 cases, with actual capacities (1, 2, 4, 10). |
| Degree 16 fibres | `D16-I8-full-quasi-transversals.md`; `D16-fibre-independent-preparation.md`, down-set inequality and star enumeration; four `D16-fibre-k*-independent.json` receipts; assembly in `D16-complete-argument.md` | Independent-support ordinary contradiction and 2,188 profiles / 124,323 nonindependent vectors excluded. |
| Cap 15 prerequisites | `LOW15-NO44-ordinary-closure.md`, dependency order and four profiles; `LOW14-NO43-ordinary-closure.md`, cross-star contradiction and graph step | N[max] ≤ 43 and an actual degree 15 point. |
| Cap 15 graph and star bridge | `LOW15-direct-Jin-A3-addon.md`; `LOW15-A3-star-fibre-reduction.md`, star support and deletion requirements | Direct A3 map with positivity proved in order; required cover counts 10, 11, 12. |
| Cap 15 complete cover domain | `LOW15-A3-cover-independent-bridge.md`, Q8 leaf criterion and exterior capacities; `replay_low15_eight_seven_covers.py`; `LOW15-eight-seven-cover-independent-replay.json` | Eight separated P8 models plus thirteen Q8 gluings; all 2,541 cases give capacities 2, 4, 10, contradicting the graph requirements. |

Older preparation notes retain their original pending-status paragraphs. The completed assemblies and later receipts named above specify what has actually finished. The direct Jin add-on replaces the initial cap-15 image argument in older notes, while retaining their later star and cover deductions.
