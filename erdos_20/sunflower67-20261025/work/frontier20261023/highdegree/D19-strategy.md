# Degree-19 strategy at cardinality 68

23 October 2026. Targeted source inspection and ordinary deductions for the next research branch; not a final review, computation replay, or Lean proof. No catalogue, LP, MILP, or certificate was rerun. The deductions below retain the frozen universal SF3 classification, isolation, B4, and the separate C5 obstruction as imported mathematical premises. H27 is an additional explicit premise wherever used. The working maximum-degree bound 19 is conditional on the preceding degree-20 exclusion being available in the same size-68 setting.

## Recommended next step

Build the support-independent 794-trace projection with the nine C5 and three P5 neighbor constraints below, and the exact two types of central P9 anchor. First try the five single-internal marker orbits, leaving all other internal members free. If individual marking is insufficient, complete the internal assignments in the source's order only after the required new exclusions have been obtained.

For the external stage, the shortest closing target is an aggregate weighted deficit at most 25. It is unnecessary to reproduce all 26 old external exclusions or the old terminal deficit bound 3 if a weaker aggregate bound already closes the new branch.

## Frozen setting and source map

Write the complete link of x as P10(Y)⊔P9(Z), where Y={0,…,5}, Z={6,…,11}, and P9 is the translate of

    015 023 034 045 124 134 135 235 245,

with deleted block B={6,7,8}. Put C=Z∖B={9,10,11}. The nineteen cones are fixed; at |F|=68 there are r=49 residual members avoiding x. Every other point is allowed arbitrary labels and support.

All source locators in this note are relative to `work/frontier20261020/prior-art68/repository/`:

| Source | Relevant content |
|---|---|
| `paper/main.tex:612–636` | Universal high-link forms at degrees 17–20, before the μ42 section. |
| `paper/main.tex:206–231,272–331` | P10/P9/P8/Q8 models, isolation, B4, and the Q8 leaf caveat. |
| `companion/upstream/MU42/TRACE_FOUNDATIONS.md:21–41,63–109` | Exact trace capacities and degree identity; D7–D9 and extension-point distinction. |
| Same file, `252–274` | High-point splits and at most two degree-≥19 points in an actual member, without μ. |
| `companion/upstream/MU42/C5_PROOF.md:61–73` | Universal sixteen-triple empty-C5 obstruction; it is a separate imported result. |
| `companion/upstream/D19/PROOF.md:26–45` | C5/P5 internal-completion bounds and central-anchor confinement. |
| Same file, `49–79` | Internal orbit sequence and the old exterior-incidence bound. |
| Same file, `102–148` | Arbitrary-support mixed-marker cover with the necessary P5 exceptions. |
| Same file, `150–182` | Terminal cone-disjointness/deficit argument. |
| `companion/upstream/D17/UNIVERSAL_EXTENSION_LEMMAS.md:5–40,77–152` | Pair/singleton resource constraints and coherent exterior families. |
| `companion/upstream/D19/certificates/INDEX.json` | Frozen old contract: F69, μ≥42, support 16–23, positive degree≥4, R42/N42, residual 50. |
| `companion/upstream/D19/scripts/model.py:31–38,50–53,68–69,108–128` | Concrete old assumptions that must be removed or replaced. |

Historical E17/E18 names in the prose mean the universal high-link forms, not the external-marker certificate files also named E17/E18M.

## 1. C5 and P5 neighbor bounds before excluding internals

For y in a component S, let I_y count members Q with y∈Q⊆S. There are nine C5 neighbors (all Y and C) and three P5 neighbors (B). Here P5 means the four-edge path on five vertices obtained from C5 by deleting one edge.

For a C5 neighbor, the inherited deletion argument gives

    d(y) − I_y ≤ 15.

Delete precisely those I_y triples from L_y. The fixed x+C5 star remains and is the only family on its six-point support. If sixteen triples remained, choose sixteen including that star and contradict the universal empty-C5 obstruction. This is valid before setting any internal variable to zero.

For a P5 neighbor, the following useful linear companion follows from the universal degree-17 theorem:

    d(y) − I_y ≤ 16.                                      (P5-delete)

After deleting the I_y internal triples, suppose at least seventeen triples remain. Choose seventeen including the four x+P5 star triples. The high-link theorem splits them into intersecting components of sizes 10+7 or 9+8 on disjoint supports. All four star triples lie in the component containing x, which therefore has at least seven members. There are no further triples containing x: the complete original link of x fixes d_F(x,y)=4. A member of this component avoiding x must cover the four-edge path. Since an internal triple has been deleted, it must use the unique two-vertex cover plus one exterior point. The pair codegree bound permits at most two such members. The component has at most 4+2=6 members, a contradiction.

This proof uses no μ threshold or outside-support bound. It sharpens the modelling presentation by providing one unconditional linear row, although the existing degree-specific inequalities below are stronger at degrees 18 and 19.

The constant 16 cannot be replaced by 15 from this triple-star information alone. Let J consist of xab,xbc,xcd,xde,bdz,bdw, with all eight indicated points distinct. J is an intersecting SF3 family: three x-star triples are controlled by the path; one non-star plus two star triples cannot have equal intersections because the latter share x; the two non-star triples share bd, which no star triple contains. Take the disjoint union of J with a P10 on new points. This is an SF3 family of size 16 with complete x-link P5 and no additional triple on {x,a,b,c,d,e}. It is a local triple counterexample to a proposed empty-P5 cap of 15, not a proposed SF4 extremizer.

On a central anchor containing y, B4 additionally gives, whenever s_y≥8,

    k_y ≤ 5+I_y   (C5),       k_y ≤ 6+I_y   (P5).

Only the central anchor receives this full prescribed-star confinement. An arbitrary marked anchor must not inherit it automatically.

If all internals are eventually excluded, these become d≤15 at nine C5 neighbors and d≤16 at three P5 neighbors. At size 68 the exterior incidence lower bound is **70**, not the old 74:

    Σ_{w outside {x}∪Y∪Z} d(w) ≥ 272−19−9·15−3·16 = 70.

Before exclusion, the linear weaker form is ≥70−4(I_Y+I_Z). Neither inequality bounds the number of exterior labels from above.

## 2. Sharper high-degree states for a P5 neighbor

For y∈B, x has degree exactly four inside L_y. In the disjoint-support high-link decomposition, the component containing x therefore cannot be P10, whose used points all have degree five. Since every central anchor through y contains x, its K_y is exactly that component and its singleton part is the opposite component. Consequently:

| d(y) | Allowed (s_y,k_y) at every central anchor | Internal consequence |
|---|---|---|
| 17 | (10,7), (9,8), (8,9) | I_y≥1; no arbitrary-I7 classification is used |
| 18 | (10,8), (9,9) | I_y=4 or 5, respectively |
| 19 | (10,9) only | I_y=5 exactly |

At size at least eight, an x-component containing the full P5 star cannot be Q8: its possible point-links are a triangle plus two-edge path, a four-cycle, or a single edge; none contains a four-edge path on five vertices. It is therefore P8 or P9, on the six points already occupied by x+P5. All k_y−4 remaining triples are internal, and the opposite component has disjoint support. This proves the exact I_y values in the last two rows.

At degree 17, if k_y=7, at most two of the three additions to the four-edge star can be exterior, giving I_y≥1. If k_y=8 or 9 the stronger exact 4 or 5 applies. In particular,

    s_y ≤ 7  ⇒  d(y) ≤ 16                 for a P5 neighbor.

This is stronger than the general small-singleton implication d≤17. It removes impossible rooted states without μ42 row enumeration.

There is also a precise completion when a P5 neighbor has degree 19. In local coordinates on Z with deleted block 012, take y=0. Completing its fixed path to C5 supplies the five required internal members

    0124, 0134, 0135, 0235, 0245.

This follows from the P9 x-component with missing x12 and its five triples avoiding x. The global labels are obtained by adding six. These are forced presences for a high-degree-state branch, not universal presences.

For a C5 neighbor of degree 19, the x-component is P9 or P10 and I_y is respectively 4 or 5. The five possible internal triples are the fixed three-vertex covers of its C5; the P9 case omits exactly one.

Finally, there is at most **one degree-19 point in each of Y and Z**. Every pair within a component is contained in an actual P10/P9 block. Two degree-19 points y,z there would give a central member containing the three high points x,y,z, contradicting `TRACE_FOUNDATIONS` E1. This is an ordinary global consistency row for degree selectors, not an assumption about minimum degrees.

## 3. Exact central-anchor data: two P9 shapes

For a central anchor R={x}∪A with A∈P10(Y),

    (s_x,k_x)=(9,10),  p_xy=2 for all y∈A,
    t_y=1 for all y∈A, with three distinct extension points.

Thus the geometric argument behind Local51 still applies at these anchors: x is large and k_x=10. Neighbor degrees are now capped at 19. The separate arithmetic theorem currently includes the more permissive cap 20 and remains a valid weaker consequence.

For A∈P9(Z), `(s_x,k_x)=(10,9)`. Begin with the rooted P10 data and remove the single cone xB. There are exactly two forms:

| Type | Number of anchors | Fixed data involving x |
|---|---:|---|
| A meets B in one point y | 6 | p_xy=1, the other two p_x*=2; all three t_*=1 |
| A meets B in two points | 3 | all three p_x*=2; t_w=0 for the unique w∈A∖B; the other two t_*=1 |

Representatives are A={6,9,10} for the first type and A={6,7,11} for the second. Extension points attached to the surviving occupied triple classes remain distinct. The counts follow by deleting one block from the displayed P10, not by a new signature catalogue.

The remaining seven central exact traces avoid x and are sums of the same projected residual variables. All anchors must use the same global degrees and internal incidences. Reusing the all-2/all-1 P10 root data for the P9 side would silently invent the deleted cone.

## 4. Internal orbit types and the old certificate sequence

The frozen `data/ORBIT_CATALOGUE.json` contains five single-member internal orbits under Aut(P10)×Aut(P9); the unequal components cannot be interchanged:

| ID | Representative | Orbit size | Cones disjoint, κ |
|---|---|---:|---:|
| I00 | {0,1,2,3} | 15 | 9 |
| I01 | {6,7,8,9} | 3 | 10 |
| I02 | {6,7,9,10} | 3 | 10 |
| I03 | {6,7,9,11} | 6 | 10 |
| I04 | {6,9,10,11} | 3 | 10 |

A first pass can mark one actual member in each orbit and leave the other internals unrestricted. The old proof first excluded I01–I03, leaving only the three I04 members sharing C={9,10,11}. Their common triple cap permits at most two. Only **after** I01–I03 have been excluded do the J1/J2 complete assignments (one or two I04 members) cover all remaining nonempty P9 possibilities.

After P9 was empty, the old proof used the 292 P10-compatible internal configurations, with size histogram 1,15,75,135,60,6 and thirteen automorphism orbits, twelve nonempty. This catalogue is a local finite geometry dependency and potentially reusable after its contents are checked; its F69 certificates are not reusable conclusions at 68.

The frozen index has 43 active certificates: 3 P9 individual, 2 P9 complete assignments, 12 P10 complete assignments, and 26 external markers. Six external cases require their marked anchor's full trace data: E09M,E11M,E15M,E18M,E19M,E21M. The old individual I01 and I03 bounds, 61889/1250 and 6236/125, are above 49 even before considering their invalid old premises. I02 and J1 are below 49, but their old contracts still prevent transferring those bounds. A positive rational margin at the new target does not repair a wrong hypothesis.

A specific obstruction to copying the new D20 internal certificate is C={9,10,11}. Removing the cone xB makes C a new transversal of P9. At an internal marker M⊆Y, the residual trace C is no longer blocked by that cone and has coefficient **zero** in the displayed D20 weighted certificate: it contains no P10(Z) block and meets none of that certificate's Y-based rows. The complementary deleted triple and its extension incidences therefore need explicit new treatment.

## 5. A smaller terminal target: weighted deficit at most 25

Let κ(Q) count the fixed cones disjoint from a residual Q. For each actual cone, the family disjoint from it is intersecting and SF4, so H27 gives

    Σ_Q κ(Q) ≤ 19·27 = 513.

Put Δ=Σ_Q max(0,11−κ(Q)). Since κ(Q)≥11−max(0,11−κ(Q)), r=49 requires

    539−Δ ≤513, hence Δ≥26.

Therefore **Δ≤25 already excludes the size-68 branch**. Seeking this aggregate inequality may avoid many individual marker exclusions. The old terminal Δ≤3 is ample but depends on its preceding geometry and cannot simply be imported.

The old arbitrary-support cover lemma remains valid at the new target: suppose every residual has at most two core points or exactly three in one component. If M={y,z,a,b} with y∈Y,z∈Z and a,b distinct exterior points is present, all residuals contain {y,z}, a, or b, except at most two extensions of one P5-exceptional triple. The pair/point caps give

    r ≤6+19+19−2+2 =44<49.

The exceptional triples in Z are {6,9,11}, {7,10,11}, {8,9,10}. They are absent P9 triples, distinct from both B and C. The old 22-member positive control demonstrates that the +2 exception term cannot be dropped. Thus, after ruling out four-core and mixed-three-core residuals, mixed-two-core residuals disappear by an ordinary argument.

The pure-three-core types deserve separate attention rather than wholesale exclusion. Once mixed pairs and all four-core/mixed-three traces are absent, pure triples on Z contribute total deficit at most 13 using only capacities: nine actual P9 triples contribute at most one each, while B and C each contribute at most two; all other pure Z triples have κ=11. This source-free arithmetic bound on that restricted geometry would leave a deficit budget of 12 for the Y side. It is a possible weaker target than reproducing all P9 external-marker exclusions. The geometry premise is essential: this is not a bound on the unrestricted baseline model.

## 6. Constraints that transfer, and those that do not

The support-independent model can use nonnegative integer multiplicities n_T for T=Q∩(Y∪Z), |T|≤4. There are 794 trace types. A four-point trace identifies the residual itself and has n_T≤1; smaller traces can have multiple distinct exterior completions and must not be assigned a binary box. A marker with an exterior point requires adding that actual point to the core (1093 trace types on thirteen points), retaining multiplicities for other outside points.

Transferable, with their stated imported premises, are the caps 19/6/2, the exact-trace capacities 10/3/1, high-link shapes, D8/D9, the universal trace margins, H27 at actual anchors, C5/P5 internal inequalities, pair/singleton resources, coherent external-family constraints, literal sunflower exclusions, and the mixed-marker cover lemma under its geometry premise. The H27 cone rows also bound the empty trace without an exterior-support cutoff. For a fixed-size feasibility formulation, impose Σn_T=49 explicitly; for maximization, do not smuggle in target-only lower bounds without declaring the contradiction setup.

Do not transfer the following without a new size-68 proof:

* μ≥42. H27 alone yields μ≥68−27=41. The old source's 42-row catalogue is therefore too narrow.
* R42.7/N42.7, positive degree≥4, co-occurring degree sum≥20, anchor degree sum≥52, or the old reciprocal/support conclusions.
* Support≤23 or ten named exterior labels. A projection must count all extensions.
* A binary residual variable for each proper trace, or exterior-point equality/distinction inferred from counts alone.
* The old 74 exterior-incidence lower bound; the valid value after empty interiors is 70.
* Internal emptiness, the 26 old marker exclusions, or their full matrices/certificates. Their `INDEX.json` contract expressly includes F69 and μ42; `PROOF.md:24` warns that the maxima are not bounds for smaller families.
* P10/P9 component exchange, generic-anchor star confinement, or isolation of all seven Q8 points. Only its five-point core has the stated general isolation property.

For example, `scripts/model.py:31–38` mixes transferable high-point/trace-margin rules with nontransferable minimum-degree/sum/μ42 constraints. Copying the predicate `good` wholesale is invalid. Calls to `local_s_candidates(...,17,7,7)` carry the old bootstrap parameters and must be replaced by the explicit universal rooted conditions, not renamed.

The suggested order is therefore: source-safe common projection → five internal markers or a direct deficit dual → only the complete internal assignments still needed → weak geometry sufficient for the mixed-marker cover → aggregate deficit ≤25. Failure of a relaxation at any stage is not a combinatorial counterexample, and success of a numerical solve is not an exact certificate until its coefficients and arbitrary-support interpretation are separately checked.
