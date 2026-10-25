# Degree17 P10 internals: ordinary bridge and pending exact replay

23 October 2026. This note interprets the fresh single-component model
`degree17_component.py` at SHA256

    1e3eaa89225246bb695740792bcaf0a5c365eb50c4212467aeb3c9569d7658d0.

The hash was checked before and after inspection. No producer import,
catalogue generation, model construction, solver, certificate replay, or
Lean command was run in this task. The twelve existing nonempty P10
receipts were read as data. The new `replay_component17.py` was statically
parsed only; execution awaits separate scheduling. No producer or already
hashed proof note was edited.

**Bridge conclusion.** Under the explicit hypotheses below, every actual
family maps to the matching component model. No bad row was found. The
existing producer receipts report negative gaps for all twelve nonempty
P10 internal orbits; exact replay of their reconstructed rows remains a
separate check. This note does not claim that degree18 is closed, that
degree17 is closed, or that a global size67 theorem has been proved.

## 1. Hypotheses and the exact cardinality guard

Let F be a finite simple four-uniform family of **exactly 68** members,
with no three distinct members having equal pairwise intersections,
including empty intersection. Assume a global point-degree cap17 and an
actual degree17 point x. For the P10 branch assume its complete link is

    L_x = P10(S) disjoint-union I7,

where S is the six-point support of the displayed canonical P10 and I7
is an arbitrary intersecting seven-triple family on support disjoint
from S. No support size, list of isomorphism types, or other
classification of I7 is assumed. The universal degree17 link theorem
supplies this alternative or the separate P9 plus I8 alternative; the
present P10 conclusion concerns the former.

The global cap17 is a conditional hypothesis. Its use does not depend
logically on having already completed a degree18 exclusion. If this
conditional theorem is later used globally, the cap must then be supplied.

The imported inputs are H27, the universal SF2/SF3 capacities and
I8/I9/I10 classification, isolation, B4, R16/high-link structure, and
the universal exact-trace margins and extension consistency arguments.
The prior mu41/cap18 crowding26 and guarded cross-star results are also
used, together with their written minimum-used-degree7 consequence.
Their guards hold because cap17 implies cap18, while H27 and |F|=68
give minimum actual closed neighborhood 41. The old mu42 minimum4 and
singleton bootstrap are not used; `r10=r9=0` remains literal.

**The exact-cardinality restriction is needed by this source.** Its row

    sum of the 41 proper nonempty trace counts <= 51-|I|

uses |F|=68, not just |F|>=68. Other geometric and mu41 arguments below
also work at larger cardinalities, but that does not justify silently
extending this model's bridge to arbitrary larger F with the same fixed
degree17 root. The producer and `D17-research.md` already specify exact68.

The P9 code paths are checked below where they differ: there the complete
root link is P9(S) plus eight disjoint-support intersecting triples,
with no need to expose their P8/Q8 shape in this projection. No P9
nonempty-orbit exclusion is asserted by this note.

## 2. Source and prior-dependency boundary

The direct frozen mathematical sources are under
`work/frontier20261020/prior-art68/`:

* `repository/paper/main.tex:188–231,272–376`: SF2 and exact-trace
  capacities, intersecting triples, isolation, B4, and the SF3 bound20.
* `repository/paper/main.tex:443–462,612–636`: R16 and the universal
  complete size17 decomposition on disjoint supports.
* `repository/companion/upstream/MU42/TRACE_FOUNDATIONS.md`, D.1–D.5,
  and its `scripts/local43.py`: universal necessary trace states.
* `repository/paper/main.tex:968–1024`: crowding26 and guarded cross-star
  theorem, including the written arbitrary-support reduction.
* `analysis/mu41/mu41-analysis.md`, Section 3: minimum used degree7,
  member sum50, and the asymmetric inequality from crowding26.
* `FOUNDATION_LEDGER.md` and
  `replay-selected-20261020/RECEIPT.json`: the earlier selected normal
  and optimized checker runs, which are reused rather than rerun here.

The producer pins local43, the paper, ledger, minimum7 bridge, selected
replay receipt, and cross15 certificate/checker. Its receipts additionally
hash `D17-research.md`, `D18-R99-bridge.md`,
`D19-singleton-I04.md`, and `C5-internal-compatibility.md`. The historical
D18 adaptation source is recorded but not imported. All local states
are regenerated with the degree17 root and cap17.

This is a selected prior-dependency chain, not a complete independent
replay of all external proofs. In particular the producer's direct
pinned file list does not itself list the crowding certificate and
checker separately; crowding26 remains the explicitly imported theorem
with the paper/ledger/selected-receipt record. The new replayer verifies
the declared file hashes and four ordinary-note hashes, and does not
claim to reprove that external theorem chain.

## 3. Internal catalogue and proper trace map

Label S by 0 through5 and x by6. The P10 blocks are

    012 015 023 034 045 124 134 135 235 245.

Let I be the **entire** internal family `F intersect binom(S,4)`, including
absence of every four-set not listed. Let B consist of the m prescribed
cones plus I, with m=10 in the active branch or m=9 for the P9 code path.
The other `k=17-m` root cones all avoid S and are not listed explicitly.

The catalogue recursively visits every increasing subset of the fifteen
possible internal four-sets, rejecting precisely an insertion that
forms a sunflower with two already present fixed or internal members.
Every actual I is reached, since each of its prefixes is sunflower-free.
Conversely, any sunflower in a completed assignment would have been
detected when its last internal member was added. The initial cones
already form a sunflower-free family.

The automorphism loop checks every permutation of S for preservation of
the prescribed block family. Its orbits preserve internal compatibility.
The constructor checks equality of covered assignments and all generated
assignments, and the expected orbit totals13 for P10 and79 for P9.
The earlier P10 catalogue has292 assignments in13 orbits under60
automorphisms; this source uses the same recursion and same component
model, independently of the new degree constraints. These finite counts
have not been regenerated in this task. The new replayer will rebuild
the catalogue and check the named representative before a certificate.

Relabeling all of F by a component automorphism, fixing x and exterior
points, moves I to its orbit representative. It does not assume that
the unknown completion is symmetric.

For each nonempty U subset S of size at most three set

    n_U = #{Q in F : x notin Q and Q intersect S = U}.

There are41 coordinates: six singleton, fifteen pair, twenty triple
counts. They retain every exterior multiplicity. Members of I are
counted separately; members with empty S trace are omitted because
they contribute to none of the represented neighbor statistics. There
is no finite exterior universe.

The box is

    0 <= n_U <= cap(|U|)-#{Q in B : U subset Q},
    cap(1)=17, cap(2)=6, cap(3)=2.

The exact trace class lies in the incidence class through U, and all
fixed incidences are subtracted once. The omitted root cones avoid S.
If two fixed A,B satisfy `A intersect B=A intersect U=B intersect U`,
every actual completion of U gives a sunflower with them. Both fixed
members are contained in S union{x}; unknown exterior labels cannot
change these intersections. An actual proper-trace completion is
distinct from a cone because it avoids x and from an internal because
its S trace has size at most three. Thus the corresponding zero box
is valid.

## 4. Fresh central local rows and all scalar restrictions

At `R={x,a,b,c}` use pair order `xa,xb,xc,ab,ac,bc`, triple counts t_i
indexed by the omitted point, and singleton order `(x,a,b,c)`. Put

    k_i=1+sum_{j not i}p_ij+sum_j t_j-t_i,
    d_i=s_i+k_i,
    N=1+sum_i s_i+sum p+sum t.

The prescribed component fixes the x-pair and x-containing triple
counts by actual intersections with its blocks. The opposite root
component fixes s_x: it is7 for P10,8 for P9. Every block of the
specified component meets the anchor triple, so the root near size
is m and `s_x+k_x=17` exactly.

The source recomputes these values. It does not reuse a D18 local
catalogue by changing a label. In particular s_x=7 in the P10 case
does **not** activate the helper's B4 clauses at x. Its degree17
high-link condition permits `(s_x,k_x)=(7,10)`, as required. In the P9
case `(8,9)` also has its actual classified rooted signature.

The free pair counts run through0–3, the free triple count through0–1,
and each neighbor singleton through0–10 subject to the helper. These
are the universal exact-trace ranges. The helper at `(emin,r10,r9)=
(17,0,0)` uses only universal high-link states, B4, incident-pair mass
at most6, the D7/D8 pair restrictions, and all rooted signatures of
size8/9/10 intersecting families. Its signature construction ranges
over every relevant P10 subfamily, Q8 at size8, every actual anchor,
and every ordering. No I7 signatures are required or assumed.

The caller adds the following necessary restrictions.

**Neighborhood41 and pair19.** H27 bounds the family disjoint from any
actual anchor by27. Hence N>=41. For a pair u,v in that anchor, members
meeting it while avoiding u,v occupy two singleton classes and one
pair class, at most23 members. Thus

    41<=d(u)+d(v)-d(u,v)+23,
    d(u)+d(v)>=19,

since their common actual anchor gives d(u,v)>=1.

**Crowding26.** Under mu41 and cap17 (hence cap18), the prior theorem
gives sum of the largest three s_i at most26. The local filter applies
to actual anchors only.

**Minimum used degree7.** The written prior bridge first obtains
d(v)>=5 from `N=d(v)+S_other+P_other+t_v`, with capacities26,9,1.
For degree5 or6, the opposite singleton sum is at least25, so at least
two opposite points have singleton count at least8. The universal
rooted I8/I9/I10 signatures in those near links force their codegrees
with v to equal one. Applying this at each link anchor makes each
triple in L_v have at least two private points. Such an SF3 has at
most four triples: each nontrivial intersection component is a star
of at most two triples, and at most two components exist. This
contradicts degree5 or6. The finite rooted check and written reduction
are the imported prior minimum7 bridge, not a mu42 bootstrap.

**Member sum50.** If S=sum s_i, crowding26 implies S<=34: the smallest
singleton is at most8. Write P=sum p and T=sum t. Then

    sum d_i=N+3+P+2T >= 2N-32 >=50,

using `P+T=N-1-S>=N-35`. This proves `sum(ds)>=50`.

**Every asymmetric degree inequality.** Fix any i, put m=d_i,
S'=sum of the other three singletons, P'=sum of their three pair
counts, u=t_i, and Q'=sum_{j not i}d(i,j)>=3. Exact counting gives

    N=m+S'+P'+u,
    sum_{j not i} d_j = S'+2P'+3u+Q'
                      =2(N-m)-S'+u+Q' >=59-2m.

Thus `sum(ds)+d_i>=59` for **every** anchor point i. No assumption
that i is minimum degree is needed. These are the four tests in code.

Finally the five trace margins according to the number of small
singletons are precisely TRACE_FOUNDATIONS D.3–D.5. Its extension
consistency test propagates the forced equalities of actual triple
extension points and rejects a collision with the required P9/P10
distinctions. Equal counts alone never identify exterior points.
Sorted deduplication only merges identical valid count rows. The
source imposes no ordering of the unknown neighbor degrees.

## 5. C5/P5 caps and the assignment-specific confinement filters

For a component point y let I_y be its assigned internal degree and
J_y count its assigned internals containing the unique P5 two-cover,
when applicable. Its fixed cone degree f_y is5 at C5 points and4 at
P5 points. Every point of P10 is C5. For P9, removing one P10 block
turns the three affected C5 point-links into four-edge paths on all
five remaining component points; the other three remain C5.

The C5 cap `d(y)<=15+I_y` follows by deleting all its internal triples
from L_y. Sixteen remaining triples with the complete C5 star would
require an internal cycle cover in their separated x-component,
contradicting the deletion. The complete-C5 argument explicitly
excludes R16 and the Q8/Q8 leaf exception at size16.

The P5 deletion cap is `d(y)<=16+I_y-J_y`. Delete only the internal
triples not containing the unique two-cover C. If seventeen remain,
the universal high-link decomposition supplies an intersecting
x-component of size at least7. Each non-star member covers the path;
surviving internals and every exterior cover contain C. Pair codegree
two permits at most two extras beyond the four stars, a contradiction.
This also proves the additional degree17 exclusion when I_y=0.

If s_y>=8, B4 makes the near family K intersecting, and

    k_y<=4+I_y+(2-J_y)=6+I_y-J_y.

An exterior extra must use C and one exterior point; the J_y internal
occurrences consume that same pair capacity in L_y. This is the
conditional P5 filter. It never treats occupied internal cover capacity
as available exterior capacity.

For `clean` and `esc`, write `V={x} union(S minus {y})`, six points.
The prescribed complete star spans all of V. The code activates the
confinement check when `s_y>=8`, or `d(y)>=17`, or C5 with `d(y)>=16`.
In each regime K is intersecting and contains all assigned internal
triples through y, as follows.

* At s_y>=8 the far family D is P8/P9/P10 or Q8. A P-type support
  avoids the link anchor; a possible deleted block also avoids it,
  so cannot occur in K. Isolation therefore makes K avoid that whole
  support. Since K spans V, D is exterior to V.
* For D=Q8 only the five-point core is isolated. Its two possible
  hub-plus-two-leaf exceptions also avoid the link anchor and cannot
  be in K. Hence K avoids the core. That core avoids V, and every
  Q8 block uses at least two core points, so none is internal on S.
  Shared leaves are allowed.
* At degree17 the complete high-link split has disjoint supports.
  Its x-component contains V and equals K, while D avoids V. The
  complete-C5 degree16 theorem gives the same assertion in its
  separate range.

Thus `links[y]`, consisting of the full star and all assigned internals,
is a subfamily of K. It must be intersecting (`clean`) and have size
at most k_y. For C5, every additional non-x triple covers the cycle
with three of its five points and is already an assigned internal.
Hence `k_y=len(links[y])`, as imposed by escape allowance zero.

For P5 an unassigned addition must be C plus an exterior point. The
`covers` test requires that C meets every member already in `links[y]`.
There are at most two additions by the pair capacity. The `esc` loop
tests one and two actual candidate triples with fresh labels7,8 for
intersection and absence of a sunflower. Any actual one- or two-point
extension can be relabeled this way, fixing V and preserving every
tested intersection. These labels do not limit all exterior support.

When activated K has size at least8, its C5/P5 rooted graph excludes
Q8. Its P-type support has six points and already contains all six
points of V, hence equals V. Every extra is internal and already
assigned, so escape allowance must be zero. At size7 only the
cover-capacity argument is used. No arbitrary I7 is classified.

The source's interval

    len(links[y]) <= k_y <= len(links[y])+(esc[y] if k_y<8 else0)

is therefore necessary in exactly the activated regimes. Complete
internal assignment, rather than selected internal presences alone,
is essential to this interval.

## 6. ONE-HIGH from actual shared exterior pools

For y in S let H_y be all triple tails outside `{x} union S` whose
lift with y lies in F, and h_y=|H_y|=n_{ {y} }. These are intersecting
SF3 families. Distinct pools are cross-intersecting: a P10 block avoids
any two component points, and a P9 retains at least one such block;
its cone would be disjoint from two disjoint lifted pool members.
Both centres avoid both tail supports. The imported cross-star theorem
therefore gives

    h_y+h_z<=15.

Indeed total size at least16 would supply an actual anchor with
neighborhood at most `d(y)+d(z)-d(y,z)+4<=38`, contradicting mu41.
All actual-family and external-centre guards are present.

A point is high for the source selector when C5 with d>=16 or P5
with d=17. The claimed at-most-one inequality is valid, including
the P9 code path.

**Two high C5 points.** Complete-C5 separation gives
`h_y=d(y)-5-I_y`, and each internal through y must be one of its five
cycle covers. For any other component point z, two of these five
four-sets contain z and are noncovers at the full C5 at z. In the
canonical labels y=0,z=1 the five are

    0245, 0235, 0135, 0134, 0124;

0135 misses z's edge24, and0124 misses z's edge35. Identifying a
point-link with the canonical C5, then rotating that cycle, transports
the calculation to every pair. A P10 is its five star triples and
five cycle covers, so this relabeling preserves its entire completion.
For full C5 points of P9 the deleted block avoids the point, giving
the same calculation. If both points are high, those two incompatible
internals are absent at each; thus I_y,I_z<=3 and h_y,h_z>=8,
contradicting HP15.

**Two high P5 points.** Their degree17 split has an x-component which
cannot be P10, since its complete point degree at x is4. A size8 near
Q8 is also impossible because its degree4 rooted graph is C4, not P5.
The possible near sizes7,8,9 have opposite sizes10,9,8, all exterior
to S. Thus both h values are at least8, again impossible.

**One high P5 point y and one high C5 point z.** If y's near size is8
or9, its P8/P9 support is the six prescribed points V. Completing its
four-edge path adds its unique endpoint edge, identifying the original
P10 completion after replacing y by x. Its non-x triples include at
least four of the five original C5 covers. Two are noncovers at z and
must be absent, a contradiction. Otherwise its near size is7 and the
opposite size is10. At z, I_z<=5 gives h_z>=6, again contradicting
HP15 with h_y=10.

Consequently the actual shared degree selectors satisfy

    sum_{C5 y}[d(y)>=16]+sum_{P5 y}[d(y)=17] <=1.

The implemented `component-one-high` row is exactly this inequality.
The argument is on actual pools before relaxing degree selectors; it
does not treat unrelated local singleton counts as separate tail families.

## 7. Every remaining row and selector equation

The actual degree of each component point lies between
`max(7,f_y+I_y)` and the proved cap. Choose its one degree selector.
The equation

    sum_{U containing y}n_U - sum_d d*delta_(y,d) = -f_y-I_y

is exact: the only other members either avoid S or are the fixed
incidences already counted. At each central anchor choose its actual
surviving local row. The three singleton, three pair, and one triple
feature equations are

    sum_{U : U intersect T=W}n_U - sum_r lambda_r feature_r(W)
       = -#{Q in I : Q intersect T=W}.

Their positions11–13,3–5,6 agree respectively with the neighbor
singletons, free pairs, and triple omitting x. The fixed cones cannot
contribute to non-x exact anchor classes. Bucket pruning retains the
actual row because all actual trace variables satisfy their boxes.
Degree-distribution equations tie these choices to the same actual
point degree at every anchor. Zero-one choices satisfy all equalities.

The upper rows have the following actual meanings.

* **Residual budget:** the51 members avoiding x partition into I,
  the41 represented trace classes, and an omitted empty-trace class.
  Hence `sum n_U<=51-|I|`.
* **Internal H27:** for an assigned internal Q, all k unspecified
  opposite root cones are disjoint from Q. Any further fixed members
  disjoint from Q are counted explicitly. The represented proper
  traces disjoint from Q are additional members of the same
  intersecting disjoint family. Thus their sum is at most
  `27-k-#{A in B:A disjoint from Q}`. Omitted empty-trace members
  could only strengthen this inequality. No I7 identities are needed.
* **HP15:** every pair of actual exterior pools has total at most15
  by Section6.
* **Total singleton pool:** the actual four-sets in all six singleton
  categories form an intersecting SF4 family, by the same avoided-cone
  argument. Hence `P=sum h_y<=27`.
* **Affine pool:** h_y<=10; if h_y=9, P<=22; if h_y=10, P<=20.
  The latter statements use the11 or10 three-transversals of P9 or
  P10 and multiplicity at most two for any tail. Therefore
  `2P+7h_y<=110` at every integer h_y from0 through10.
* **Whole-pool lower:** at an anchor singleton size9 or10, P-type
  isolation gives h_y=s_y. At size8 a P8 gives equality, while Q8
  guarantees only six core-only exterior triples, h_y>=6. Its leaves
  may meet S. Equality also holds in the complete-C5 degree16 or
  high-link degree17 regimes, and when s_y>=8,k_y>=8 forces the
  near P-type support to equal V. These are exactly the code guards;
  no s<=7,k>=8-only equality is imposed.
* **Conditional pool:** at any one anchor through y,
  `P+5*[s_y=9]+7*[s_y=10]<=27`, using the preceding equality and
  P<=22 or20. The penalties are not summed over different points.

The whole-pool rows use the same h_y at every anchor, with its certified
lower bound averaged over the local selectors. An actual one-row
choice satisfies each; all such witnesses remain admitted by the
convex relaxation.

Finally, `pair_constraints` uses the universal pair/singleton resource
table from `D18-structural-tools.md` and the frozen D17 extension lemmas.
At a C5 point, all pair traces through y have pairwise-intersecting
exterior edges; every singleton tail meets each edge. Each edge has
multiplicity at most two. The exterior graph is a star or triangle;
pair/triple codegree capacities give

    b=0,1,2,3,4,5,6  =>  h<=10,10,8,5,4,2,1.

These imply `b<=6` and `5h+9b<=59`. At a P5 point the same statement
is valid separately after excluding either one of its two cover
vertices from the possible partner points; then two partner points
cannot be the unique two-cover, so a path edge avoiding them exists.
The source creates exactly these two restricted pair pools. It does
not impose the C5 argument on the entire P5 pair pool.

## 8. Existing twelve producer reports

The following values were read from `degree17/P10_001.json` through
`P10_012.json`; they are **producer-reported** arithmetic, not new replay
results. All use the source hash above and scale10^10. The orbit sizes
are the unchanged P10 internal-catalogue orbit sizes. A successful
scheduled replay must independently recompute every H, minimum and G
against the hash-matched model.

| Case | Complete internal representative | Orbit | Columns | H | Minimum | G=H−Minimum |
|---|---|---:|---:|---:|---:|---:|
| P10_001 | 0123 | 15 | 1381 | -1428571432 | -30 | -1428571402 |
| P10_002 | 0123,0134 | 30 | 258 | -10526315789 | 0 | -10526315789 |
| P10_003 | 0123,0145 | 30 | 820 | -4363636364 | -7 | -4363636357 |
| P10_004 | 0123,0245 | 15 | 159 | -10000000000 | 0 | -10000000000 |
| P10_005 | 0123,0134,0145 | 30 | 116 | -11666666667 | 0 | -11666666667 |
| P10_006 | 0123,0134,0245 | 60 | 106 | -20000000000 | 0 | -20000000000 |
| P10_007 | 0123,0134,1245 | 30 | 119 | -13548387096 | 0 | -13548387096 |
| P10_008 | 0123,0145,2345 | 10 | 520 | -10000000000 | 0 | -10000000000 |
| P10_009 | 0123,0245,1345 | 5 | 107 | -10000000000 | 0 | -10000000000 |
| P10_010 | 0123,0134,0145,1235 | 30 | 103 | -20000000000 | 0 | -20000000000 |
| P10_011 | 0123,0134,0145,2345 | 30 | 103 | -20000000000 | 0 | -20000000000 |
| P10_012 | 0123,0134,0145,1235,1245 | 6 | 99 | -20000000000 | 0 | -20000000000 |

The empty case P10_000 reports2475 columns and gap0. The producer
found a feasible relaxation there; this does not construct an actual
SF4 family. This note makes no exclusion of that case.

## 9. Exact replay contract and conclusion boundary

`replay_component17.py` is a separate adaptation of the already used
component18 replayer. It accepts one receipt and a deadline at most20
seconds. It selects the current or frozen source by exact SHA256,
checks source constants and receipt metadata for root17, cap17, mu41,
minimum7, outside=`17-component`, and zero bootstraps, and checks the
complete canonical internal representative. It checks every pinned
dependency and the four recorded ordinary bridge hashes before model
reconstruction and again afterward. Its premise digest records exact68.

The model is rebuilt through `build`, never `run` or `matrix`; numerical
producer entry points are disabled. No SciPy or solver is needed. Every
row coefficient, RHS, and finite box endpoint must be a Python integer,
including those with zero certificate weight. Dimensions, live local
catalogue sizes, 41 trace coordinates, and the all-zero objective and
target are checked. Sparse certificate weights must have unique valid
indices and strictly positive values in the precise order `(A,E,-E)`.

For their weighted row sum write q for the complete column vector and
H for the weighted RHS. The source's finite boxes give

    minimum=sum_j min(l_j*q_j,u_j*q_j),
    minimum <= q*z <= H.

Thus `G=H-minimum<0` contradicts feasibility. Equality rows may be used
with either sign because they are equalities. All original selector
columns are retained; the artificial phase-one slack column is absent
from this final contradiction. The replayer compares exact H, minimum,
G and the negative flag with the receipt, records model/q hashes and
the named weighted rows, and verifies all bound inputs remain unchanged.

Only a static AST parse of the new replayer was performed in this task.
There is no new D17 replay receipt yet. If the scheduled twelve replays
all verify negative gaps, their complete catalogue coverage together
with the family-to-model bridge above excludes every nonempty P10
internal assignment under Section1's exact68/cap17 hypotheses.

That conditional implication does not require a completed degree18
proof. Applying it to a larger global argument still requires the
explicit cap17 hypothesis, the imported structural/prior results, and
the separate treatment of empty P10 and the other high-link branch.
