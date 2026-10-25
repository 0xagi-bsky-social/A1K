# Q8 internal obstruction: ordinary structural research

23 October 2026. This note inspects saved discovery receipts and proves new
necessary inequalities on arbitrary support. It is not a final review or a
global closure claim. No model was imported, no solver was run, and no model
source was edited. The inspected source is frozen v2, SHA256
`682c441de23f9008fa1cec531a888c12138bbce5ea867a50dd23fb81c5f17cd0`.

Write the complete degree-18 root link as P10(Y) plus

    Q8(h,k; {a,b,c}; l,m),

where Y={0,...,5}, h=6, k=7, a=8, b=9, c=10, l=11, m=12, and x=15.
Its triples are h or k with each triad pair, and hkl,hkm. The first component
and the Q8 support Z are disjoint. F is finite simple SF4 with empty cores
forbidden. The active target additionally assumes |F|>=68 and Delta<=18,
so mu>=41 under H27. The universal intersecting I8/I9/I10 classification,
isolation, B4, and universal R16 classification are stated dependencies below.

## Decoding the remaining internal types

| Case | Representative | Description | Original v2 exact-box upper |
|---|---|---|---:|
| I02 | {h,k,a,l}, mask 2496 | both hubs, one triad, one leaf | 50 |
| I04 | {a,b,c,l}, mask 3840 | all triad, one leaf | 50 |
| I05 | {h,k,l,m}, mask 6336 | both hubs, both leaves | 50.0000000623 |
| I06 | {h,a,l,m}, mask 6464 | one hub, one triad, both leaves | 51.44444449 |

These values do not exclude residual 50. The small excess in I05 is the
recorded rounded dual box correction, not a strict certificate below 50.
The parent has separately excluded I00,I01,I03,I07 and reports that forbidding
those orbits leaves these four obstructions. In particular I00 comprises

    {h,k,a,b}, {h,k,a,c}, {h,k,b,c}.

Every original saved primal for I02,I04,I05,I06 has both hub degrees exactly
16. These are relaxation points, not asserted actual families. The new hub
lemma below shows that degree 16 is impossible after I00 is absent.

## Complete triangle-plus-path star lemma

Let L be any SF3 family containing exactly the following five triples through
a point x:

    xab, xac, xbc, xkl, xkm,

where a,b,c,k,l,m are six distinct points different from x. Suppose that L
contains none of kab,kac,kbc. Then

    |L| <= 15.                                           (HUB)

The assertion is on arbitrary support. It imports the universal R16 theorem,
whose sixteen-member template has used point degrees four and six only.

First, any triple U avoiding x and meeting all five displayed triples must
contain at least two of a,b,c to meet the triangle edges ab,ac,bc. Its remaining
one point must meet both kl and km, hence must be k. Thus the only possible
such triples are kab,kac,kbc. Consequently every intersecting subfamily that
contains all five star members consists of exactly those five when the three
completions are absent.

Suppose |L|>=16 and choose sixteen members including the five star members.
Call this subfamily L0. The degree of x in L0 is exactly five, since the five
displayed triples are the complete x-star of L. If L0 has no member with eight
disjoint companions, it is an R16. The universal R16 template has no point of
degree five, so this is impossible.

Otherwise choose an actual A in L0 whose disjoint family D has size at least
eight. D is intersecting, and B4 makes K=N_L0[A] intersecting. Both have size
at most ten, and |D|+|K|=16.

If D is P8, P9, or P10, isolation makes K avoid its whole support. Indeed every
deleted-block exception lies on the support of D, which avoids A, so it would
be in D rather than K. If x lay in that P-type support, its complete five-edge
point-link would be a C5; the prescribed triangle disjoint from a two-edge
path is not a C5. Hence x is outside that support and all five star members
belong to K. The first paragraph then gives |K|=5, whereas |D|<=10 and
|D|+|K|=16, a contradiction.

The remaining case is D=Q8, of size eight, and K also has size eight. If K is
P8, its support is disjoint from that of D. To see this, any D member meeting
the P8 support would be a deleted P10 block by isolation; intersection of D
would force every D member to meet that support, restricting all eight to at
most two deleted blocks. This is impossible. The five x-star members therefore
lie in one part. They cannot lie in P8 because a degree-five point there has a
C5 point-link. If they lie in Q8, the literal graph identifies its other hub
as k, its triad as a,b,c, and its leaves as l,m. Its three non-x completions
are kab,kac,kbc, contrary to the hypothesis.

Finally suppose both D and K are Q8. K avoids the core of D: the two exceptional
triples allowed by Q8 isolation lie wholly on the support of D, avoid A, and
cannot be in K. Conversely D avoids the core of K. A D member meeting that
core would have to be one of K's two exceptional triples, hence lie in the
support of K; but every D member contains at least two points of the D core,
which is disjoint from that support. Thus the two Q8 families can share only
leaves. A shared leaf has total degree two, so x of degree five is not shared.
Its five star members lie in one Q8, again requiring kab,kac,kbc. This final
contradiction proves (HUB).

### Consequences for the two actual Q8 hubs

Apply (HUB) in the complete triple link L_h. The five x-star members are
xab,xac,xbc,xkl,xkm, because the complete root link has exactly the prescribed
Q8 component. The absent triples kab,kac,kbc are precisely the lifts of the
three I00 members through h. The same reasoning holds with h,k exchanged.
Therefore, once I00 is excluded,

    d(h)<=15,             d(k)<=15.                       (HUB0)

More generally let G count the three I00 members actually present. Deleting
their three possible link triples leaves a family with the same complete
five-star and no completion. Hence the unconditional rows are

    d(h)-G<=15,           d(k)-G<=15.                     (HUB-G)

These statements do not require the minimum-used-degree-seven bridge, a
support bound, mu41, or Delta18. They do require the cited universal R16
classification in addition to I8/I9/I10, isolation, and B4. At the present
stage the already proved I00 exclusion makes the scalar cap15 available.

At a central anchor through h, write s for its exact singleton size at h and
k_h for its near link size. If s>=8, B4 makes the near family intersecting.
If d(h)>=17, the universal high-degree split gives the same fact. In either
regime the five star members are present, and the first paragraph of (HUB)
shows that its additional members are exactly the I00 completions. Every one
of those completions meets every displayed star anchor: two triad pairs
intersect, and each completion contains k. Thus

    k_h=5+G                                               (HUB-K)

in those regimes. The analogous equality holds at k. This is stronger than
merely requiring the rooted graph to occur in an I8/I9/I10 template, and does
not classify arbitrary I7 families.

## Safe Q8 whole-component singleton pools

For v in Z, define H_v to be the actual triple tails with v union T in F and
T avoiding {x} union Z. Let h_v=|H_v|. Each H_v is intersecting SF3, using a
prescribed cone through v to rule out two disjoint tails. Thus h_v<=10.

Q8 has exactly one two-point transversal, the hub pair {h,k}. Therefore for
every other distinct v,w in Z there is a Q8 block avoiding both. Its cone
shows that H_v and H_w are cross-intersecting: disjoint tails would give a
three-member empty-core sunflower with that cone. The centres avoid all tail
supports. The already imported cross15 theorem therefore gives

    h_v+h_w<=15          for all {v,w}!={h,k}.            (Z-HP15)

There is no automatic inequality of this kind for the exceptional hub pair.
However each of the two centre sets Z\{h}, Z\{k} has all pairs cross-intersecting.
The corresponding actual four-set unions are intersecting and H27 gives

    sum_(v!=h) h_v<=27,      sum_(v!=k) h_v<=27.          (Z-POOL)

Within either six-centre pool the ordinary large-tail consequences also hold:
if one h_v=9, its pool is at most22; if h_v=10, its pool is at most20. Triple
transversals of a P9/P10 and multiplicity at most two prove these statements
exactly as for the Y pool. In particular each such pool P satisfies

    2P+7h_v<=110          for every centre v in that pool.

For I04, the actual marker {a,b,c,l} avoids both hubs and lies wholly in Z.
It is disjoint from every tail in H_h or H_k. It therefore supplies the
missing cross-intersection guard for the two hub pools. All seven categories
then form an intersecting actual four-set family: full Z-POOL<=27, all 21
Z-HP15 rows, and the corresponding full-pool large-tail and affine consequences
are valid in that marked branch. This uses an actual member avoiding the
hubs, not a false assertion that Q8 has no two-point transversal.

### Whole-Z lower bounds at the hubs only

The five prescribed link triples through x in L_h cover every point of
{x} union (Z\{h}). Thus the ordinary singleton-isolation argument extends to
the hubs despite their point-link not being C5 or P5. At any central anchor
through h,

    h_h>=ell(s),    ell(8)=6, ell(9)=9, ell(10)=10,
    ell(s<=7)=0.                                        (Z-HUB-LOWER)

For P8/P9/P10 far families, whole-support isolation gives h_h=s. For Q8 at
s=8 only its core is isolated; its six core-only triples are exterior to the
entire prescribed seven-point support, giving six. Its leaves can still
overlap that support. The same applies at k. At d(h)>=17, universal disjoint
support separation gives h_h=s. No equality is inferred solely from k_h>=8
when that near component may be Q8.

These whole-Z lower bounds are not automatically valid at triad points or
leaves. Their prescribed x-stars do not cover every other Z point. Applying
the full-component identification there would require another argument.

## A separate global small-trace H27 row

Let S=Y union Z, without the marked exterior point. The residual members with
at most two S-points form an intersecting family. If two were disjoint, their
union would contain at most four S-points. But a transversal of P10(Y) plus
Q8(Z) requires at least 3+2=5 S-points, so a prescribed cone avoids both,
creating an empty-core sunflower. Hence the universal row is

    sum_(|t intersect S|<=2) n_t <= 27.                  (SMALL-H27)

This remains valid with an actual marked exterior point in the represented
trace universe: test core size, not total represented trace size. Other
unrepresented exterior points remain arbitrary. The row does not forbid
larger-core residuals elsewhere in F.

The original saved four obstruction primals put only 13.90,15.69,15.80,19.06
members in this small-trace pool, respectively, so this particular row does
not cut those displayed points. It remains a valid general improvement and
may help later marked stages. The hub cap15 cuts every displayed point.

## What the current exact dual equalities say

For I02, the receipt has scale 10^10, H=49 times that scale and box correction
one times that scale. Thus it proves upper50, exactly. At residual50 every
positively weighted upper row must be tight. In particular all ten Y-block
triple incidence rows are tight, the exact pair {k,l} at anchor {x,h,k,l}
has size three, the singleton counts at k,l there sum to sixteen (the third
crowding singleton is the fixed root value ten), and the exact singleton at
a of the marked anchor {h,k,a,l} has size ten. This last class is an actual
P10 tail family. The receipt also uses central-selector equalities; the
listed tight upper rows alone are not asserted to classify all equality
families.

For I04, H=50 times scale and the correction is zero. Its positive upper rows
include the triad triple-codegree bound, several central crowding26 rows,
the exact pairs {h,l},{k,l} at anchor {x,h,k,l}, and the exact singleton at m
of anchor {x,h,k,m}. Equality therefore forces the last singleton to size ten.
The displayed primal realizes a whole-Z singleton pool h_m=10 by placing all
ten P10(Y) block extensions at m; its total whole-Z pool is about20.762 and
would violate the valid full-pool-at-h_m=10 bound20 in the I04 branch. The
identity of this whole-component singleton with the central size-ten class
is not yet proved for all equality families at a leaf; the observation about
the displayed primal must not be promoted to that missing bridge.

For I05 the stored integer upper is 500000000623/10^10, and for I06 it is
514444444900/10^10. Neither is an exact upper50 equality certificate. Their
positive dual supports are useful diagnostic information, but no automatic
tightness implication at residual50 is claimed.

## Sources and remaining work

The source definitions, labels, orbits, original dual weights and primal
projections are from `degree18_p10/Q8-catalogue.json` and the four
`Q8-I0*-internal-*.json` receipts. The ordinary isolation/B4 proof and the
R16 template are in the frozen prior-art `paper/main.tex:272-331,451-459`;
the cross15/crowding guards are at lines968-1024. Prior replay provenance is
recorded in `PRIOR_DELTA18_UNLOCK.md` and `prior-delta18-unlock.json`.

The new useful ordinary result is the complete triangle-plus-path star lemma
and its hub cap15 after I00 exclusion. The pool rows above have separately
stated cross-intersection guards. None of these arguments claims that the
remaining four Q8 cases, or the whole degree-18 branch, are closed before the
corresponding new numerical bounds and their exact replay evidence exist.
