# Fixed-AHS deletion stability: working proof and evidence note

Date: 2026-10-23. This is an ongoing research note, not a final review or a
publication artifact. Older source records remain frozen. No Lean claim is made.

Let `SF4` mean a finite simple family of four-element sets containing no three
distinct members whose three pairwise intersections are equal. Let `I27` mean an
intersecting SF4 family with 27 members. Partition a fixed nine-element set `S`
into triples `X,Y,Z`. Write `P(X)` for the three two-element subsets of `X`, and
put

\[
 A=\{p\cup q:p\in P(U),\ q\in P(V),\ U,V\in\{X,Y,Z\},\ U\ne V\}.
\]

Thus `A` is the fixed 27-member AHS family. Everything below concerns this fixed
family and its copies. It assumes neither a nine-point support bound for general
families nor a classification of all I27 families.

## Saved finite evidence and its status

The existing `trace_probe.py/json` treats all 256 subsets of `S` of size at most
four: 27 existing AHS blocks, the empty trace, and 228 nonempty nonmember traces.
The existing `stability_certificate.py/json` treats all 101,584 subsets of at
most five omitted AHS blocks. The separate C++ record
`omission_probe.stdout.txt` agrees on all six maxima below and additionally
records degrees six and seven. No computation was rerun to prepare this note.

For exactly `d` omitted blocks, the recorded maximum sum of the individual
admissible nonempty trace-fibre caps is:

| d | omission masks | maximum extra weight | total bound under H27 |
|---:|---:|---:|---:|
| 0 | 1 | 0 | 54 |
| 1 | 27 | 0 | 53 |
| 2 | 351 | 2 | 54 |
| 3 | 2,925 | 9 | 60 |
| 4 | 17,550 | 11 | 61 |
| 5 | 80,730 | 18 | 67 |

These are exact finite diagnostic receipts. A sum of independent fibre caps need
not be attained by an actual SF4 extension; the displayed maxima are maxima of
the weighted trace relaxation. The JSON field referring to an ordinary proof in
`STABILITY.md` is metadata, not evidence that such a file exists or that its
proof was checked. This note records the ordinary mathematical bridges explicitly.

## The trace and fibre bridge

For an ambient SF4 family `F`, put `D=A\F`, `d=|D|`, and let `t=E∩S` for each
`E∈F\A`. A blocker edge for `t` is a pair `a,b∈A` with
`a∩b=a∩t=b∩t`. Both endpoints cannot survive, since `a,b,E` would form a
sunflower. Consequently `D` must be a vertex cover of the blocker graph of `t`.
This applies to arbitrary exterior points: no assumption about `∪F` is used.

For `d≤5`, the only possible nonempty nonmember trace profiles, up to permuting
the triples and their points, are `(2,0,0)`, `(2,1,0)`, and `(2,1,1)`. All other
profiles have six vertex-disjoint blocker edges, explicitly recorded in the
local certificates. A six-edge matching cannot be covered by five deletions.

For trace `p` of profile `(2,0,0)`, the blocker graph is `K3,3`, between the
blocks `p∪q` with `q∈P(Y)` and those with `q∈P(Z)`. There are six AHS blocks
containing `p`, so at least one survives. The exterior two-sets in this fibre
must pairwise intersect, since two disjoint exterior two-sets together with a
surviving block containing `p` give a sunflower. They have no three-edge star,
as that is itself a sunflower after adjoining `p`. A simple intersecting graph
is a star or a triangle: if two edges are `uv,uw` and a further edge avoids `u`,
it must be `vw`; any other edge meeting all three is one of these three. Thus
the fibre has at most three members.

A trace of profile `(2,1,0)` has an exterior singleton, so three members in its
fibre would form a sunflower. Its cap is two, improved to one if a surviving
AHS block contains the trace: that block and two fibre members would have common
pairwise intersection equal to the trace. A `(2,1,1)` trace is already a four-set
inside `S`, so its cap is one by simplicity.

If H27 is the external input that every intersecting SF4 family has size at most
27, the empty-trace fibre also has size at most 27. Indeed, two disjoint members
of it and any surviving AHS block would be three disjoint four-sets, a forbidden
sunflower. Hence the empty-trace fibre is intersecting. Therefore the recorded
weighted caps imply `|F|≤(27-d)+27+w(d)`, giving the last column of the table.
H27 is an explicit dependency; this note does not prove it.

## An ordinary local rigidity argument

Suppose `G` is I27 and `|G∩A|≥22`, so `d=|A\G|≤5`. An empty trace is impossible
because `G` is intersecting and at least one AHS block survives. The six-matching
profiles are impossible as above. A `(2,0,0)` trace misses all nine blocks
between the other two triples, so it is also impossible.

A `(2,1,1)` trace, represented by `0136` on triples `012,345,678`, has the five
disjoint blocker pairs

\[
(0134,0135),\quad(0145,0178),\quad(0167,0168),\quad
(3467,3568),\quad(3567,3468).
\]

Here strings denote sets of point labels. In addition, the AHS block `4578` is
disjoint from the trace and is not an endpoint of any of those pairs. Thus an
intersecting extension requires at least six omissions, again impossible.

It remains to consider a trace `p∪{b}`, with `p∈P(X)` and `b∈Y`. Put
`q0=Y\{b}`, and let `q1,q2` be the two pairs in `Y` containing `b`. Intersection
forces the three omissions `q0∪r`, `r∈P(Z)`. Independently the blocker graph is
the disjoint union of the star with centre `p∪q0` and leaves `p∪r`, `r∈P(Z)`,
and the edge joining `p∪q1` to `p∪q2`. These six blocker vertices are disjoint
from the three forced omissions. With at most two further omissions available,
one must delete the star centre and one endpoint of the isolated edge. Thus
`d=5`, and, relabelling `q1,q2` if necessary,

\[
D=\{q0\cup r:r\in P(Z)\}\ \cup\ \{p\cup q0,\ p\cup q1\}.
\]

In the graph whose vertices are the nine pairs in `P(X),P(Y),P(Z)` and whose
edges are AHS blocks, this deletion set has exactly one full row of three edges
between two parts, namely `q0` to `P(Z)`. Every admissible intersecting `(2,1,0)`
trace must have such a forced full row. That row determines its singleton `b`
and its doubled triple `X`; the two remaining deleted edges determine its pair
`p`. Hence there is at most one possible new trace. The surviving block
`p∪q2` contains it, so its fibre has at most one member. This yields
`|G|≤22+1=23`, contradicting `|G|=27`.

Thus there are no new members at all, and `G⊆A`; equality follows from the two
cardinalities. We have proved the local statement

\[
G\in I27,\quad |G\cap A|\ge22\quad\Longrightarrow\quad G=A.
\]

This does not prove every I27 family is an AHS copy, nor force an arbitrary I27
family to have large overlap with an AHS copy.

## Ordinary proof of the weighted caps

Identify the AHS blocks with the edges of `K3,3,3`, with vertex parts
`P(X),P(Y),P(Z)`, and regard `D` as a graph with `d≤5` edges. A row consists of
the three possible edges from a fixed vertex to one other part. For a vertex
`v`, let `k_v,l_v` be the numbers of deleted edges in its two rows. Let `f` be
the number of full rows (rows with three deletions), and put

\[
B=\sum_v[k_v(k_v-1)+l_v(l_v-1)],
\qquad
C=\sum_v[\mathbf1_{k_v=3}l_v(3-l_v)
          +\mathbf1_{l_v=3}k_v(3-k_v)].
\]

Let `q` be the number of admissible `(2,1,1)` traces. The total weighted cap is
exactly

\[
W(D)=B+3f+C+q. \tag{1}
\]

To see this directly, a `(2,0,0)` trace is admissible precisely when at least
one of its two rows is full, by its `K3,3` blocker graph. Both cannot be full
with five deletions. Its weight three therefore contributes exactly `3f`.

For a `(2,1,0)` trace `p∪{b}`, examine the row from `p` to `P(Y)`, with `k`
deletions, and its opposite row to `P(Z)`, with `l` deletions. If the opposite
row is not full, admissibility requires deletion of the star centre
`p∪(Y\{b})`. Its weight is then the number of deletions among the other two
row edges: zero means inadmissible, one gives cap one, and two gives cap two.
Summing over the `k` choices of a deleted centre gives `k(k-1)`. If the opposite
row is full, any centre is allowed and the corresponding sum is `2k`. The
additional contribution is `2k-k(k-1)=k(3-k)`. Summing both row directions at
every vertex proves (1).

There are at most two full rows. Indeed two distinct rows share at most one
edge. If two full rows exist with at most five deleted edges, they must lie in
the same bipartite piece on opposite sides and share their joining edge. Their
union is exactly five edges, forming a double star. Its two centres have row
degree three and its four leaves have row degree one. There is no third full
row, `B=12`, and `C=0`.

If `q>0`, choose one admissible trace `p∪{b,c}` with `p∈P(X), b∈Y, c∈Z`.
Its five disjoint blocker pairs consist of:

- one pair of XY blocks, both containing `p` and `b`;
- one pair of XZ blocks, both containing `p` and `c`;
- the pair `p∪(Y\{b})`, `p∪(Z\{c})`;
- two pairs wholly within the YZ piece.

Covering them takes exactly five deletions, one endpoint from each pair. Thus
the deletion counts in the three bipartite pieces are `1,2,2` in some order.
No row is full, so `f=C=0`; each two-edge piece contributes at most two to `B`,
giving `B≤4`.

Moreover `q≤12`. Fix the piece containing the single deletion. For any
admissible `(2,1,1)` trace, its doubled triple must be an endpoint part of this
piece, since the piece between its two singleton triples requires two
deletions. There are two choices of doubled triple. Its doubled pair is fixed
by the endpoint of the sole deleted edge. The singleton in the other part of
that piece must lie in the other endpoint pair, giving at most two choices;
the last singleton has at most three choices. Consequently
`q≤2·2·3=12`. In this case (1) gives `W≤4+12=16`.

It remains to bound the cases with `q=0`. The sum of the 18 row degrees is
`2d`. If `f=0`, every row degree is at most two, and `B≤2d`. If `f=1`, writing
`n2` for the number of degree-two rows gives `B=6+2n2`. The row-degree sum
yields `n2≤d-2`, hence `B≤2d+2`. Only the other row at the full row's centre
can contribute to `C`; its degree is at most two, so `C≤2`.

These observations give the individual small-deletion bounds:

- `d=0,1`: no blocker graph can be covered, so `W=0`.
- `d=2`: `f=q=0`; two distinct edges share at most one row, so `B≤2`.
- `d=3`: if `f=0`, `W=B≤6`. If `f=1`, all deletions form that row,
  so `B=6,C=0`, and `W=9`.
- `d=4`: if `f=0`, `W=B≤8`. If `f=1`, start with its three-edge star
  and consider the fourth edge. In the same bipartite piece, it touches at
  most one leaf and raises `B` by at most two, with `C=0`. In another piece,
  it raises no row degree above one except in the original piece (which it
  does not touch), so `B=6`; it can give `C=2` only by using the star's centre.
  Either way `B+C≤8`, hence `W≤11`.
- `d=5`: if `q>0`, the preceding argument gives `W≤16`. Otherwise `f=0`
  gives `W≤10`, `f=1` gives `W≤12+3+2=17`, and `f=2` gives `W=18`.

Thus the ordinary upper bounds are exactly `0,0,2,9,11,18`. To see sharpness
for this weighted relaxation, choose vertices `x1,x2,x3∈P(X)` and
`y1,y2,y3∈P(Y)`. Starting from no deleted edges, use the successive deletion
sets

\[
\varnothing;\quad
\{x1y1\};\quad
\{x1y1,x2y1\};\quad
\{x1y1,x2y1,x3y1\};\quad
\{x1y1,x2y1,x3y1,x1y2\};\quad
\{x1y1,x2y1,x3y1,x1y2,x1y3\}.
\]

Formula (1) gives the claimed values; `q=C=0` in each example. This establishes
the displayed maxima by ordinary finite graph arguments, independently of the
enumeration's assertions. The diagnostic receipts corroborate these values.

## Explicit small matching witnesses

For completeness, the five excluded profiles have the following six disjoint
blocker edges. Each entry `(a,b)` is checked simply by intersecting its two
four-sets with the displayed trace. Strings denote sets; the triples are
`012,345,678`. Permuting triples and points transports these witnesses to every
trace in the corresponding profile.

| trace | six blocker edges |
|---|---|
| `0` | `(0134,0267), (0234,0167), (0135,0268), (0235,0168), (0145,0278), (0245,0178)` |
| `03` | `(0134,0235), (0234,0135), (1234,3567), (1235,3467), (0145,0267), (0245,0167)` |
| `036` | `(0134,0235), (0234,0135), (1234,3578), (1235,3478), (0145,0278), (0245,0178)` |
| `012` | `(0134,0167), (0234,0267), (1234,1267), (0135,0168), (0235,0268), (1235,1268)` |
| `0123` | `(0134,0135), (0234,0235), (1234,1235), (0145,0167), (0245,0267), (1245,1267)` |

The other three blocker graphs used above can be found by direct intersection:
`K3,3` for `(2,0,0)`; the disjoint star and edge for `(2,1,0)`; and exactly the
five disjoint pairs displayed in the rigidity argument for `(2,1,1)`. This is
an eight-profile calculation on the fixed AHS support, not a classification of
ambient extremal families.

## Scope still open

The ordinary local results now have explicit proofs: the weighted caps, their
conditional total bounds, and I27 rigidity at overlap at least 22. The missing
global bridge is a reason that a hypothetical large SF4 family must contain an
AHS copy or an I27 member with the required overlap with such a copy. Neither
these arguments nor the finite records establish that bridge. In particular,
they do not rule out all 68-member SF4 families.

One useful contrapositive is now available: under H27, a 68-member SF4 family
would meet every AHS copy in at most 21 blocks. Indeed, overlap at least 22
would put it in one of the six rows of the table, all of whose total bounds
are at most 67.

The omission amendment records `d=6,7` separately and permits the extra external
rank-three cap H10 there. Those degrees are outside this ordinary proof, which
uses no H10. No Lean compilation or axiom audit has been done, and no final
review or publication step has been undertaken.
