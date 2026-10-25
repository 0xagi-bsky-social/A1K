# Complete C5 stars at degree sixteen and above

23 October 2026. Ordinary structural deduction for the degree-19 research branch, conditional on the pinned universal SF3 classification, B4, and isolation. This is not a final scholarly review, computation replay, or Lean formalization. No solver or classification computation was run. The size-16 exception and the Q8 shared-leaf issue are checked explicitly below.

## General structural lemma

Let L be a finite simple SF3 family containing a point x whose **complete** point-link is a five-cycle on a five-point set V. Thus x has degree exactly five, and the five members through x are precisely x plus the cycle edges. Put U={x}∪V. If |L|≥16, then L is the disjoint-support union of two intersecting families. The component K containing x has support exactly U, and every member of K avoiding x is a three-vertex cover of the cycle.

In particular, if I counts the members of L contained in V, then all these I members belong to K and cover the cycle, and

    |K|=5+I.

The other component avoids U. Every actual anchor triple A containing x has N_L[A]=K and D_L(A)=L∖K. These conclusions hold even when |K|=6 and the other part has size ten; no classification of an arbitrary intersecting six-triple family is assumed.

## Proof at size sixteen

Use ρ(L)=max_A #{T∈L:T∩A=∅}.

**The R16 alternative ρ≤7 is impossible.** The universal R16 theorem gives four hubs and two disjoint triads. Every hub has degree six (three triples with its triad and three triples on the hub set); every triad point has degree four. There is no point of degree five. Equivalently, the model's hub point-links are two disjoint triangles and its triad point-links are four-cycles. Thus this model cannot have the assumed complete C5 star. This step uses the actual R16 classification, not an unsupported assertion that every sixteen-triple family decomposes.

**For ρ≥8, B4 gives two intersecting parts.** Choose A with at least eight disjoint members and write H=D_L(A), K′=N_L[A]. Each part has at most ten members; their sizes are 10+6, 9+7, or 8+8 (up to order). At least one part has size at least eight and is therefore a P10, P9, P8, or Q8.

**If either part is a P-type, the supports are disjoint.** Isolation says that a member of the other part meeting its six-point support must be one of its deleted P10 blocks. If the P-type part is H, its support avoids A, so any deleted block also avoids A and cannot belong to K′. If the P-type part is K′, then A is a block of that P-type; every deleted block meets A because all P10 blocks intersect, so it cannot belong to H. Thus no block in the opposite part meets the P-type support. This argument works for a completely arbitrary opposite I6 or I7.

**The remaining Q8/Q8 case is impossible without assuming disjoint leaves.** If no side is a P-type, both sides are Q8 of size eight. A hub point of Q8 has a triangle in its point-link; a triad point has a C4 in its point-link. Neither can be a subgraph of the assumed complete C5 at x. Hence x cannot be a core point in either Q8. A peripheral point has degree at most one in each Q8, so its total degree is at most two, even if it is a shared leaf. This contradicts degree five. No isolation claim about all seven points of Q8 is used.

We therefore have an intersecting partition with disjoint supports. All five triples through x lie in the same part, so that part contains U in its support. Every additional triple in that part avoids x and meets each star triple. It must cover C5 with at least three vertices of V; since its size is three, it is contained in V and is a cycle cover. Hence the whole part is supported exactly on U. A member of L contained in V cannot belong to the other part with disjoint support, proving the assertions about I.

## Sizes seventeen through twenty

The universal high-link theorem directly gives disjoint-support intersecting decompositions at sizes 17–20. The same C5 covering argument proves the lemma. The universal SF3 bound twenty exhausts the remaining sizes. No neighborhood threshold, maximum support, or SF4 cardinality hypothesis is used.

## Translation to a central C5 neighbor in the SF4 family

Let the complete link of the degree-19 center x be P10(Y)⊔P9(Z). For any C5 neighbor y (all of Y and points 9,10,11 of Z), the pair {x,y} has codegree exactly five. In L_y, the point x therefore has precisely the prescribed C5 star, on the five other points of y's component S.

Let I_y=#{Q∈F:y∈Q⊆S}. If d_F(y)≥16, the general lemma yields, for **every central anchor** through y,

    k_y=5+I_y,
    s_y=d_F(y)−5−I_y,

and the singleton family is supported outside {x}∪S. Every internal member through y must have Q∖{y} a three-vertex cover of the fixed C5. There are no additional non-internal members in the component containing x.

This is stronger than the earlier conditional use of B4 at s_y≥8. The necessary upper bound

    k_y≤5+I_y

may safely be applied whenever **s_y≥8 OR d_F(y)≥16**. The s≥8 case follows directly from B4 and the covering argument; the degree≥16 case uses the fully checked alternatives above.

For the sharper version, let G_y count only internal members whose residual triple is a C5 vertex cover. Then k_y≤5+G_y in either regime. There is also an unconditional deletion consequence

    d_F(y)−G_y≤15:

remove the G_y cover-internal triples from L_y. If sixteen or more triples remained, the general lemma would require a non-star member in the component of x (every component has at least six members) and would require it to be an internal cycle cover, but all such triples were removed. Thus the residual link has at most fifteen members. Separately, the presence of even one non-cover internal member forces d_F(y)≤15, since the general lemma at degree≥16 would put that member in the intersecting star component.

These statements rely on the **complete** pair-link. If one has only five prescribed cones and allows further triples containing x in L_y, the C5 point-link premise has not been established.

## The singleton Y pattern M={0,1,2,3}

Assume M is the only internal member on Y. Its residual triples at points 0 and 2 are not C5 covers; its residual triples at 1 and 3 are covers.

| y | M∖{y} | Cover status | Consequence |
|---|---|---|---|
| 0 | {1,2,3} | Misses edge {4,5} in the point-0 C5 | d(0)≤15 |
| 1 | {0,2,3} | Covers all five edges | d(1)≤16; equality forces (s,k)=(10,6) |
| 2 | {0,1,3} | Misses edge {4,5} in the point-2 C5 | d(2)≤15 |
| 3 | {0,1,2} | Covers all five edges | d(3)≤16; equality forces (s,k)=(10,6) |
| 4,5 | no internal through y | No cover-internal member exists | d(y)≤15 |

The old saved receipt `degree19/Ypattern01-Z.json` has degree values d0=d2=15 and d1=d3=16. Its dual has positive coefficient on the C5 bound at point 3, where M is a valid cover. Therefore simply replacing the caps at 0 and 2 does **not** cut that saved fractional point. The stronger near/far decomposition does cut its unrealizable degree-16 states.

Specifically, if d(1)=16, its component containing x consists exactly of the five prescribed cones through 1 and M. Every other member through 1 avoids all other points of Y and has a triple tail outside {x}∪Y. There are exactly ten such tails. The same holds for point 3 at d(3)=16. Hence all residual pair traces containing 1 or 3 and another Y point are supplied solely by M. This rules out the saved fractional residual incidences for pairs {1,4}, {1,5}, {3,4}, and {3,5}, which are approximately 1.7271,0.4375,0.6167,0.4375.

## Synchronization if both d(1)=d(3)=16

Let H_y be the complete family of triples T outside {x}∪Y such that {y}∪T∈F. The preceding lemma gives |H_1|=|H_3|=10, so each is a P10.

For distinct y,z∈Y, there is a prescribed P10 block avoiding both. A triple in H_y and a triple in H_z cannot be disjoint, since together with that cone they would form an empty-core sunflower. Thus all H_y are pairwise cross-intersecting.

A P10 has no two-point transversal, and its three-point transversals are exactly its ten blocks. Consequently every member of H_3 belongs to H_1; equality of the two size-ten families follows. Call the common P10 H.

Each T∈H already occurs as two SF4 members, {1}∪T and {3}∪T, saturating its triple codegree two. For y∈{0,2,4,5}, the same cross-intersection argument gives H_y⊆H, and saturation then gives

    H_0=H_2=H_4=H_5=∅.

This is a concrete synchronized-tail constraint. The saved fractional point violates it: its projected exact-Y singleton totals are H4=1 and H5=2, while its H1≈7.8354 and H3≈8.9458 also fail the forced value ten. These contradictions concern the saved relaxation point. The deductions do not by themselves prove that every actual synchronized P10 configuration is impossible, and no claim is made that a full marked-anchor local table alone will close the branch.

## Safe row implementation

For C5 central rows, activate the internal cost max(0,k_y−5) when `s_y≥8 or d_y≥16`, not only when `s_y≥8`. The ordinary proof above permits right-hand side I_y, or the sharper G_y if cover compatibility is tracked literally. At I_y=1 and d_y=16 this forces k_y≤6; with s_y≤10 it gives exactly k_y=6,s_y=10. The near-side geometry also forbids all additional residual pair/triple traces on the component support.

The implication “d_y≥16 ⇒ every internal is a cover” can be used to filter complete internal assignments or degree states. Do not impose d≤15 merely because an internal member exists: the compatible cases y=1 and y=3 demonstrate why the cover test matters.

## Frozen source locators

All paths are relative to `work/frontier20261020/prior-art68/repository/`.

* `paper/main.tex:206–231`: P10/Q8 models and the I8/I9/I10 classification.
* `paper/main.tex:272–331`: isolation, B4, and explicit warning that Q8 leaves may be shared.
* `paper/main.tex:443–462`: definition of R16 and its four-hub/two-triad classification. The point-degree calculation used here is immediate from its displayed block formula.
* `paper/main.tex:612–636`: size-17–20 high-link decomposition.
* `companion/upstream/MU42/C5_PROOF.md:65–69`: the size-16 separated-case support argument, including arbitrary opposite part and the two-Q8 exception. This note replaces its empty-internal premise by compatibility with all star edges and explicitly excludes R16 using the full classification.
* `companion/upstream/D17/UNIVERSAL_EXTENSION_LEMMAS.md:85–122`: cross-intersection of exterior families, multiplicity two, and the P10 three-transversal characterization used in synchronization.

Assurance remains ordinary source-backed mathematics conditional on the imported universal theorems. No new certificate, end-to-end Lean theorem, independent reproduction, or branch closure is claimed by this note.
