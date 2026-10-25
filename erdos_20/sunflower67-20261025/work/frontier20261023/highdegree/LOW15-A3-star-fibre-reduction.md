# Cap15: the A3 image and the remaining deletion-cover interface

24 October 2026. Ordinary development, conditional on the named earlier
results. This is not a final review or a Lean theorem. All support statements
below are proved from the geometry; no ambient point cutoff is imposed.

## Premises and the exact image

Let F be a simple three-sunflower-free four-uniform family of size68 and
maximum point degree15. Use H27, the imported Jin homomorphism theorem,
and the newly established `LOW15-NO44-ordinary-closure.md`, which gives
N(Q)<=43 for every actual Q. The disjointness graph G is triangle-free,
has independence number at most27, and minimum degree at least25.

Jin's strict k=4 threshold holds because 25*14=350>5*68=340. Removing
empty fibres by the ordinary cyclic image-reduction map recorded in
`LOW15-NO9-fibre-route.md` gives a surjective image A_k with k<=4.
A1 and A2 contradict respectively 68<=54 and 136<=135. A4 is also
impossible: its eleven adjacent-fibre masses are all at least25 but
their sum is4*68=272<275. Thus the image is A3.

Use vertices modulo8, with edges at differences3,4,5. Write a_i>0 for
the fibre masses and b_i=a_(i+3)+a_(i+4)+a_(i+5). The adjacent fibres
form an independent set, so 25<=b_i<=27. Consequently

    r_i=b_i-25 in {0,1,2},   sum_i r_i=4,
    a_i=7+r_i+r_(i+3)+r_(i+5).                         (1)

The inverse follows by expanding b_i+b_(i+3)+b_(i+5)=68+a_i. No
assertion that G is a complete blowup is made.

## The support of a degree15 star

Fix an actual point x of degree15, and let t_i count its star members
in fibre i. Put S={i:t_i>0} and q_i=sum_(j adjacent i)t_j. Since a
star member has no disjoint star neighbour, its graph degree is at most
b_i-q_i. Therefore q_i<=r_i for each i in S. In particular

    sum_(i in S) t_i*deg_(A3[S])(i)
      =sum_(i in S) q_i <=sum_(i in S) r_i <=4.       (2)

If S is independent, it is contained in a cyclic three-index window
(the general window proof is in `LOW15-NO9-fibre-route.md`). That
window has mass at least25. Its at least25-15=10 nonstar members are
distinct actual four-covers of the complete link L_x.

Suppose S is not independent. Formula (2) permits only a single edge,
two disjoint edges with every endpoint weight1, or a three-vertex path
with all three weights1, together with possible isolated indices. An
induced component with at least three edges already contributes at
least6, and in the two-edge path the cost is twice its centre weight
plus its two leaf weights.

For a chord edge {0,4}, the only common nonneighbours outside its
endpoints are2,6, which are adjacent. If both are occupied there are
two disjoint edges, all four weights are1, and there is no remaining
isolated index. If just one is occupied, let e=t_0+t_4. The endpoint
r values consume at least e of the total4. Neither contributes to
the isolated fibre's formula (1), so its mass is at most11-e. The
total star size is then at most11. A single edge with no isolated
index is smaller still.

For a three-vertex path, its centre needs r>=2 and its leaves each
need r>=1; these consume all4. Normalize its centre to0. Its leaves
are a pair from {3,4,5}. The common nonneighbour set outside the path
is respectively {2}, empty, or {6} for leaf pairs {3,4},{3,5},{4,5}.
Every such isolated index has mass7 by (1), because it is nonadjacent
to all three positive-r sites. The total star size is at most10.

It remains to take an edge of difference3 or5, normalized to {0,3}.
Its common nonneighbours are1,2, which are nonadjacent. Zero or one
occupied index among them again gives a total at most11. Therefore
every nonindependent degree15 star has exactly

    S={0,1,2,3},   A3[S] has only the edge {0,3},
    t_0,t_3 in {1,2},   t_1,t_2>=4.                    (3)

The endpoint bound follows from q_0=t_3<=r_0<=2 and its reciprocal.
To obtain the interior lower bound, put e=t_0+t_3. The remaining
r budget is at most4-e, so each interior mass is at most11-e.
Their star weights sum15-e, forcing each to be at least4.

## Concrete one- and two-deletion requirements

For (3), let D_3 be the actual set of t_3 star cones lying in fibre3.
Every nonstar member in fibres0,1,2 meets every cone outside D_3,
since its image can be adjacent to no occupied index except3.
By (1), a_0+a_1+a_2=25+r_5. Hence there are at least

    a_0+a_1+a_2-(15-t_3)=10+t_3+r_5                  (4)

distinct actual four-covers of L_x minus D_3. Symmetrically, deleting
the t_0 actual cones in fibre0 leaves at least10+t_0+r_6 covers
from fibres1,2,3. These are actual set counts, not candidate-support
counts and not a presumed complete image blowup.

Thus a one-deletion cover bound10 rules out an endpoint of weight1,
and a two-deletion cover bound11 rules out an endpoint of weight2.
Bounds for both deletion sizes exclude every nonindependent support.
The common full-cover fibres1,2 supply at least

    3+t_0+t_3-r_0-r_3

full covers, which need only be between1 and3. A small full-cover
bound alone consequently does not exclude (3).

## Independent supports for the classified links

For an 8+7 link, the ordinary argument in `LOW15-NO9-fibre-route.md`
gives at most4 actual full covers. It uses P8/Q8 isolation, B4 and
the pair-codegree6 bound; it does not require an I7 support cutoff.
This contradicts the independent-star lower bound10.

For rho(L_x)=7, `LOW15-R15-rho7-classification.md` gives R16 minus
one triple, conditional on the stated arbitrary-support I7 catalogue.
Use disjoint five-point sides X={u,v} union D and Y={a,b} union E,
where D,E are triads, and the canonical R16 triples

    {uP,vP:P in choose(D,2)} union choose({u,v,a,b},3)
      union {aP,bP:P in choose(E,2)}.

Each six-core still has at least five triples after the single
deletion, and no point covers five of its triples. A full four-cover
therefore uses exactly two points in X and exactly two in Y, with
no exterior point.

An intact six-core has precisely four two-covers: its hub pair and
the three triad pairs. If the deleted triple is central, both cores
are intact. Selecting two triad pairs misses every remaining central
triple; all other combinations use at least one hub pair. This gives
exactly1+3+3=7 full four-covers. The three remaining central triples
alone do have a common hub; the argument uses the restricted core
two-cover choices, rather than asserting otherwise.

If the deleted triple is u+d_1+d_2, the first core acquires exactly
one additional two-cover {v,d_3}. Indeed a pair with precisely one
hub must use the opposite hub v and the point common to the two
remaining u-core pairs, namely d_3; the original four possibilities
are otherwise unchanged. All four central triples remain. The new
pair can be completed only by the opposite hub pair {a,b}, because
an E-pair would leave just one selected hub and miss the central
triple avoiding it. There are exactly8 full covers. Symmetry handles
every outer deletion.

Thus rho7 links have at most8 literal full covers, again fewer than
the10 required by independent support. This calculation uses no
actual-family codegree bound. It says nothing about the unclassified
rho<=6 links.

## Remaining finite interface

The nonindependent classified cases now require only the actual-cover
counts after one and two deletions in (4). Any proposed support census
must count arbitrary exterior completions: at least13 link triples
remain, and the universal link point-degree bound6 means two points
meet at most12. Thus every ambient four-cover uses at least three
points of the full link support W. If C3 is the set of supporting
three-covers and P4 the supporting four-covers containing none of
them, global triple codegree2 and simplicity give the valid union bound

    actual covers <=2*|C3|+|P4|.

Any cases exceeding10 or11 need further actual-family arguments; a
raw finite count must not be silently truncated to the desired bound.
The rho<=6 size15 classification remains a separate open route.
