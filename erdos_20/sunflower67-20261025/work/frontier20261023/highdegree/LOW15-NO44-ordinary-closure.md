# Cap15: every actual neighbourhood has size at most43

24 October 2026. Ordinary proof development, written in the existing Oct23
work directory. This composes the completed rho7 classification with the
literal N44 argument. It is not a final review, a solver certificate, a
Lean theorem, or a global67 result. No new execution was performed here.

## Statement and dependency order

Let F be finite, simple, four-uniform and free of three-member sunflowers,
including empty core. Assume |F|=68 and Delta<=15. Under H27, the universal
B4/I8/isolation results, the stated HP15/crowding imports, and the complete
I7 catalogue with its arbitrary-support trace obstruction, one has

    N_F(R)<=43 for every actual member R of F.

The ordinary dependencies are used in the following acyclic order.

1. H27 makes every disjoint complement intersecting of size at most27,
   hence N(R)>=41 for every actual R.
2. `LOW15-mu41-research.md` excludes P10 at cap15.
3. `LOW15-large-singleton-core.md` gives the triangle, row6, and omitted-
   triple row4 lemmas; `LOW15-two-low-core.md` excludes N45, giving N<=44.
4. `LOW15-NO9-fibre-route.md` then excludes every P9 point-link subfamily,
   giving all exact singletons<=8.
5. `D16-P8-no-two-cover-exclusion.md` applies at cap15: its degree and
   neighbourhood hypotheses are only Delta<=16 and N<=45, with no-P9 and
   the named universal imports. It excludes the P8 type whose two omitted
   blocks intersect in one point. Thus every actual intersecting I8 used
   below is two-cover P8 or Q8.
6. `LOW15-N44-N43-core-route.md` reduces a hypothetical N44 anchor to four
   scalar profiles using only these ordinary local lemmas.
7. `LOW15-N44-Q8-leaf-R15-reduction.md` reduces every one of these profiles
   to an actual15-member SF3 link with rho exactly7 and a forbidden local
   degree pattern.
8. `LOW15-R15-rho7-classification.md` classifies precisely that rho7 domain
   as R16 with one triple removed. Its proof imports the already complete
   I7 catalogue, not a conjectured R15 catalogue or the unresolved rho<=6
   domain. The classification was inspected here against the literal H6,
   H7 and H2 arguments and the frozen paper's cardinality-independent H2
   reduction at `paper/main.tex:574--611`; no additional premise is needed.

The finite I7 evidence and its arbitrary-support boundary are documented in
`D17-I7-classification-route.md`: seven six-point types cover all1860 labelled
families, the seventh-point type is supplied by the ordinary support proof,
and all175 mixed traces have actual forbidden-pair witnesses. The new
independent coverage receipt is `D17-i7-coverage.json`; this assembly does
not rerun it or elevate it to Lean verification. The prior cross-star and
crowding provenance is `PRIOR_DELTA18_UNLOCK.md`.

## The four profiles and the literal obstruction

If N(R)=44, label R={0,1,2,3} so the singleton counts are(7,7,8,8).
All four root degrees equal15, all exact root triples vanish, and in pair
order01,02,03,12,13,23 one has

    A: (1,3,3,3,3,0),    B: (2,2,3,3,2,1),
    C: (3,1,3,3,1,2),    D: (3,2,2,2,2,2).

At a low root i=0 or1, A_i=R minus i has exactly seven disjoint triples
in the complete15-member link. Its three point degrees are1+p_ij. Hence
the distinguished triple has degree pattern(2,4,4) in A,C, or(3,3,4) in B,D.

If that link has rho8, choose its eight-disjoint-triple family H and its
intersecting seven-member complement K. The distinguished A_i cannot lie
in H: every remaining P8/Q8 block has a point of degree5, while all three
degrees in A_i are at most4. If H is P8, support separation would give
eight disjoint companions, not seven. Thus H is Q8, K avoids its core,
and A_i contains precisely one of its leaves. The corresponding pair
category has one edge, the Q8 hub pair, disjoint from the common triangle
of the other two categories of size3. This precise(1,3,3) form is proved
without classifying K.

It cannot occur in B,D, whose low-root rows have no singleton category.
In C, the two high-root triangles agree via their shared size2 category;
the alleged singleton edge would have to lie both on and off that triangle.
Thus both low-root links in B,C,D have rho7.

In A, if both low-root links had the exception, their common singleton
pair member E={0,1,a,b} would have pair codegrees

    d01=2, d0a=d0b=d1a=d1b=5, dab>=3,

and triple codegrees d01a=d01b=1, d0ab=d1ab=2. Exact neighbourhood
inclusion-exclusion would give

    N(E)<=4*15-(2+5+5+5+5+3)+(1+1+2+2)-1=40,

contrary to N(E)>=41. Hence at least one low-root link in A has rho7 too.

Every hypothetical N44 anchor therefore yields a15-member SF3 link with
rho7 and an actual triple of degree pattern(2,4,4) or(3,3,4).

## The rho7 theorem excludes both patterns

R16 has four hubs of degree6 and two triads whose six points have degree4.
Deleting a hub triple lowers three hub degrees to5 and leaves every used
point of degree at least4. Deleting an outer hub-plus-triad-edge triple
lowers its hub to5 and exactly its two triad endpoints to3; all other hub
degrees remain6 and all other triad degrees remain4. In particular no
used point has degree2.

The only remaining way to see two degree3 points is the second deletion
type. These points are precisely the two endpoints of the deleted edge.
Their only surviving common triple uses the other hub assigned to that
triad. That hub retains degree6, so an actual(3,3,4) triple is impossible.
Neither required pattern exists. This excludes N44 and, with N<=44
already proved, establishes the stated N<=43 conclusion.

There is no use of a classification of rho<=6 links: A_i itself has seven
disjoint triples, so the upper bound rho<=7 is automatically equality.
There is also no inference that near size8 alone is intersecting; the only
such intersection assertion comes from B4 at a separately chosen rho8
witness, exactly as detailed in the preceding reduction note.

## Current boundary

The disjointness graph consequently has minimum degree at least25. This
alone does not contradict order68 and independence bound27; the Wagner
image remains numerically possible. An exclusion of N43, hence N<=42,
would raise the minimum degree to26 and permit the ordinary A3 fibre-sum
contradiction already recorded in `LOW14-NO43-ordinary-closure.md`.
That additional exclusion is not proved here.

## Frozen source identities used by this assembly

| Source | SHA256 |
|---|---|
|LOW15-R15-rho7-classification.md|151e0cde17bdf12f3ab348248a47d721edadc23baf6aee8e32aeacb0971056e6|
|LOW15-N44-Q8-leaf-R15-reduction.md|1a5cef2332cfdaeb5a10a20a2206f58d01303e597d46993b418027f135c1f100|
|LOW15-N44-N43-core-route.md|25fdfcf37e85b76a1e656ab241860456b8286a640487a06c0ee99dcd291c50e1|
|D16-P8-no-two-cover-exclusion.md|d2e9688375e99a5a21b2f1bdfaa70ad96dc1ad3ae1ed75695d6bb1c2595eda1d|
|LOW15-two-low-core.md|6f09a59a3705b93c38f21a6a5eb3de725540d321876ed620bb56f95fd7130bb1|
|LOW15-NO9-fibre-route.md|576a463ffc3c86138e53d6919f75ead7274a6dd46401a69bc3b6ca8e3b41e0b1|
|D17-I7-classification-route.md|a86e80d8377f24218194461c7e2dd92ffe44c3d6b4a505240bd050f129dcb504|
|PRIOR_DELTA18_UNLOCK.md|25b65f695264ae0dbcd5d97b8e66eac421cccbb9970eaf20cc8692886f855b89|
