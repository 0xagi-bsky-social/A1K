# Degree 17 through the universal I7 catalogue

23 October 2026. Ordinary structural research and preparation of an unexecuted
projection, not final review or publication. No D17 full model or solver has
been run in this task. A separate small solver-free finite census was executed
once, in 0.134 seconds, to independently cover the I7 catalogue.

## All eight I7 types are transferable

The eight families H0,...,H7 in the frozen paper's universal R16 proof classify
**every intersecting simple SF3 family of seven triples**, on arbitrary support.
The classification is not conditional on being embedded in R16, on mu42, or
on the global gate appearing elsewhere in the R16 wrapper's contract. The
ordinary support reduction and the finite catalogue each precede the R16
case split. Thus they apply to the opposite I7 component in a complete
degree-17 link P10 plus I7.

The complete degree-17 link alternatives are P10 plus one of these eight
types, or P9 plus P8-i1, P8-i2, or Q8. Their supports are disjoint by the
universal high-link theorem. These eleven forms are root-link possibilities,
not finite cutoffs on the ambient support of the four-uniform family.

### Ordinary arbitrary-support reduction, reconstructed

Let H be an intersecting SF3 family with seven distinct triples.

Its maximum point degree is at most six. Degree six is impossible: its SF2
point-link is two disjoint triangles; any triple avoiding the point would
need at least two vertices from each triangle to meet all six members.

If a point has degree five, its complete SF2 link is C5 or a triangle disjoint
from a two-edge path. A triple avoiding that point is a three-vertex cover of
this graph. A C5 has no two-cover, so all three vertices lie on the cycle,
putting H on six points. In the triangle-plus-path case, the cover consists
of two triangle vertices and the middle path vertex. The two triples avoiding
the degree-five point choose two of the three triangle pairs. This is the
unique seven-point family H7, namely Q8 with one core-only triple deleted.

Now suppose all degrees are at most four. If there is a degree-one point l
in luv, each of the other six members meets {u,v}. Let a,b,c count members
using only u, only v, and both, respectively. The u-only and v-only residual
edge families are intersecting SF2: two disjoint edges together with luv
would form a sunflower. Hence a,b<=3. The pair uv has global triple-family
codegree at most two, one occurrence already being luv, so c<=1. Consequently
the only possibilities, after exchanging u,v, are (3,3,0) and (3,2,1).

In the first case the two three-edge residual families are triangles. Their
cross-intersection forces the same triad, giving six support points. In the
second case the three-edge family is a triangle on D, and each of the two
opposite residual edges is a two-transversal of that triangle, hence an edge
of D. The extra common member uvr has r outside D, because each pair u-d for
d in D is already used twice. Thus this is H7 on seven points. Under the
current maximum-degree-four assumption this latter alternative cannot occur
(one hub has degree five), but identifying it explicitly also covers the
degree-one case without that assumption.

If there are no degree-one points and the maximum degree is at most four,
let b,c,d count degrees two, three, four and let B count pairs of codegree two.
Intersection of every pair of triples gives

    2b+3c+4d=21,     B=b+3c+6d-21.

For a used point w, its SF2 link has maximum degree at most two and matching
number at most two. At link sizes two, three, four, the numbers of degree-two
link vertices are at least zero, one, two. Summing gives 2B>=c+2d, hence
2d>=2b+c. If n=b+c+d is the support size, then 21=3n-b+d, so n<=7. Equality
would force d=b and c=0, making n=2b even, impossible at seven. Thus n<=6.
Finally support at most five cannot contain seven SF3 triples: their 21 pair
incidences exceed the twenty supplied by ten pairs of capacity two.

This proves that six points or the single seven-point H7 case exhaust the
possibilities, independently of a finite search.

### Exact templates and finite coverage

| Type | Seven triples | Six-point orbit size |
|---|---|---:|
| H0 | 012 034 134 035 235 145 245 | 120 |
| H1 | 012 034 234 135 235 145 245 | 360 |
| H2 | 012 134 234 135 235 145 245 | 60 |
| H3 | 013 024 134 125 235 045 345 | 240 |
| H4 | 023 124 134 125 235 045 345 | 360 |
| H5 | 014 234 025 125 035 145 345 | 360 |
| H6 | 134 234 125 035 135 045 245 | 360 |
| H7 | 023 024 034 124 134 015 016 | seven-point case |

The previous `terminal.r16` normal and optimized executions both called
`check_seven.verify`. Their saved outputs explicitly report 1860 labelled
six-point families, the seven orbit sizes above, one seven-point type,
15360 complementary-pair selections, and all175 mixed traces checked. The
current `verify.py`, `check_seven.py`, and `seven_certificate.json` match the
actually replayed package byte for byte. Both saved output hashes match the
Oct20 replay receipt. Those facts were checked here by reading and hashing;
the old suite was not rerun.

The new independent `D17_i7_coverage.py` imports no upstream code and uses a
different exhaustive domain: all77520 seven-subsets of the twenty triples on
six points. It filters pairwise disjointness and literal equal-intersection
sunflowers, obtaining exactly the same1860 families. Independently generated
S6 orbits of H0,...,H6 are disjoint and have exactly this union. It checks H7
against the ordinary seven-point model, verifies every template directly,
and independently checks all175 allowed/forbidden mixed traces and their
actual-pair witnesses. Its result is saved in `D17-i7-coverage.json`.

This finite census certifies its stated finite domain. The preceding ordinary
argument supplies completeness on arbitrary supports. Neither layer is Lean,
and normal/optimized execution of the old checker alone would not establish
independence of its mathematical assumptions.

The certificate SHA256 is
`fe172301b201819c029d9a1b7e8931f516cbd90aa978977118b7853b2ead7164`;
the upstream checker hash is
`f8d157274c5625fac692e6fd015c6d23a28b212cd82da0e0397ff00e30382705`.
The independent checker receipt binds its source hash and certificate hash.

## Existing D17 P10-internal evidence

The thirteen `degree17/P10_*.json` records were inspected. P10_000, the empty
internal pattern, has phase-one slack zero and exact gap zero. Every nonempty
pattern P10_001 through P10_012 has a strictly negative recorded exact gap.
There are no surviving nonempty patterns in those diagnostic records.
The gaps begin -1428571402, -10526315789, -4363636357, -10000000000, and all
remaining nonempty gaps are also negative.

This note has not independently rebuilt those models or replayed their
certificates. A full projection that assumes P10-side internals absent must
record that D17 component exclusion as an explicit dependency. It must not
substitute the D18 root-degree calculation for it. In the P9+I8 branch, Y-side
internals remain free unless separately excluded.

## Safe projection route

The prepared `degree17_full_projection.py` uses root degree17, global cap17, mu41 and
residual target51, with arbitrary exterior trace multiplicities. Its root
models are precisely the eleven forms above. Component automorphism groups
are computed in S6 or S7; they act separately because the component sizes
differ. Four-core and mixed-three-core-plus-one-actual-exterior markers retain
all actual point identities. Z internals are free. Y internals are absent
only in the P10 branch under the explicit D17 exclusion premise.

The frozen D18 v4 trace architecture transfers after replacing the root and
global degree caps and adjusting geometry by literal component graph. The
universal exact-anchor caps, H27, pair-degree19, crowding26, prior cross15,
and prior minimum-used-degree7 remain valid at cap17. The minimum-degree
bridge uses mu41 and cap at most18; no support-23 cutoff is needed.

The rooted intersecting graph filter can now safely include k=7 as well as
8,9,10, **only when the near family is known intersecting**: s>=8 by B4, or
d>=17 by the universal separated-link theorem. The seven-family filter must
use all eight templates, including H7, rather than only seven-subfamilies of
P10. Merely knowing k=7, outside those regimes, does not justify it.

P5/C5 cuts require the complete literal graph and the correct six-point
support. The triangle-plus-P3 hub lemma applies when that complete graph
uses all other six points of a seven-point component, including the relevant
H7 hub, not only Q8. Its three actual internal cover completions are charged
explicitly. P9 pair/singleton rows use the two restricted partner pools at a
P5 vertex; the unrestricted C5 pair row must not be applied to a P5 vertex.

The small-core H27 row remains valid: the P10/P9 component has transversal
number at least three, and any I7/I8 component has transversal number at least
two (a common point would have triple-family degree at least seven, exceeding
six). Guarded whole-component Z pools use actual blocks avoiding the centre
pair. No unconditional Q8 or arbitrary-I7 whole-pool cross-intersection is
assumed.

The exact CLI kind names are `P10-H0` through `P10-H7`, `P9-P8-i1`,
`P9-P8-i2`, and `P9-Q8`. Its default action is a catalogue; `--build-only`
builds one relaxation and `--solve` explicitly requests one solver call of
at most30 seconds. The marker prefixes are `IY` for Y internals (present only
in the P9 branch catalogue), `IZ` for opposite internals, `E4_` for mixed
four-core sets, and `E3_` for mixed-three-core plus one actual exterior point.
Shared degree-distribution ties remain optional and default off. The prior
crowding/minimum7/cross15 imports are required in this prepared version.

No invocation of this full constructor has occurred, including no module
import, no catalogue generation, and no model build. Standard-library AST
parsing confirms only source syntax. On first use, the I7 loader requires
the pinned certificate hash and a matching independent finite-census receipt;
it does not silently rerun that census. Numerical receipts hash these sources,
the ordinary route note, the prior R16 outputs, and the adaptation source.
For P10 branches they additionally record hashes and stated negative gaps of
all twelve D17 internal exclusion receipts, explicitly distinguishing these
imported records from an independent replay of their model arithmetic.

All finite-box dual arithmetic is over all trace and selector columns with
Python integers; the comparison is against residual51, not the D18 target50.
The output directory is `degree17_full`, and immutable receipt stems include
the complete-link kind, marker, and source/premise fingerprint. Z/internal
assignments or forbidden markers remain literal additional branch premises.

## Source boundary

The ordinary classification and high-link decomposition are at frozen
`paper/main.tex:463-514,612-636`. Finite provenance is in
`companion/terminal/r16/src/check_seven.py`, `src/verify.py`, and
`results/seven_certificate.json`, with the already saved
`replay-selected-20261020/RECEIPT.json` and its two R16 outputs. The minimum7
bridge is `analysis/mu41/mu41-analysis.md`. All these are prior-art premises,
not newly claimed classification discoveries.

The remaining task is numerical exclusion of the full arbitrary-support
degree17 branches using valid premises, followed by exact arithmetic replay.
Neither the catalogue nor this route note claims that exclusion.
