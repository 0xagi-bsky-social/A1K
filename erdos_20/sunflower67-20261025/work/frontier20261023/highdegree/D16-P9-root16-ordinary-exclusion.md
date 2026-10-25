# Ordinary exclusion of a P9 component at a degree16 root

23 October 2026. Ordinary research proof development, not a final review
or Lean formalization. No solver, model construction or finite support
enumeration was run. Every unrepresented exterior point is unrestricted.

**Claim.** Under the stated imported premises, a size68 SF4 family of
global degree cap16 cannot have a degree16 point whose link contains
P9. This closes the P9-plus-I7 alternative for a degree16 root. It does
not by itself exclude P9 components at smaller root degrees or the
remaining degree16 eight-plus-eight alternative.

## Dependency order and complete link

Let F be finite, simple, four-uniform and free of three-sunflowers,
including empty core. Assume |F|=68 and Delta<=16. H27 gives mu>=41.
Use the following already stated ordinary results in this order:

1. `D16-P10-ordinary-exclusion.md`: no point-link contains P10.
2. `D16-NO47-ordinary.md`, independently checked in
   `D16-NO47-independent-check.md`: every actual Q has N(Q)<=46.
3. `P9-disjoint-complement22.md`: if a complete point-link has an
   isolated P9 component on W, then every actual Q outside {x} union W
   has at most22 disjoint members.

The third proof uses HP15 with both centres outside both actual tail
supports, including a separate application for either exceptional P9
transversal. It retains all surviving outside link triples; it does not
replace a contained P9 star by a complete point-link.

Suppose d(x)=16 and L_x contains H=P9=P10 minus B on W, |W|=6. No-P10
and isolation give the complete disjoint-support decomposition

    L_x=H union K,       |K|=7,       supp(K) disjoint W.

K is intersecting: two disjoint K triples and any H triple would be
three disjoint link triples, hence a sunflower in F with core x. No
classification of I7 is used.

## The outside pool exists and internal four-sets are absent

Partition the52 actual members avoiding x by exact W trace size, with
counts O,H_1,P_2,E_3,I_4 for sizes0,1,2,3,4. Write

    D=H_1+2P_2+3E_3+4I_4.

The trace0 and trace1 classes together are intersecting: any disjoint
pair from them has a combined W trace of size at most2, avoided by a
P9 block. That block's actual x-cone would be disjoint from both.
Consequently

    O+H_1<=27.                                            (1)

Initially D<=6*16-27=69, subtracting the27 incidences of the nine
prescribed cones. The identity

    104=2*52=D+H_1+2O-E_3-2I_4

implies O>=8, so an actual outside member Q exists.

For every such Q, the family I=D(Q) is intersecting and has size at
least22 by NO47. Its complete x-link is H union K', where K' consists
of the K triples whose x-cones avoid Q. If K' were empty, the complete
P9 intersecting-family bound20 would contradict |I|>=22. Thus some
K-cone avoids Q. Any actual four-set contained in W would then be
disjoint from Q and that K-cone, making an empty-core sunflower. Hence

    I_4=0.                                                (2)

Three support points of P9 have complete C5 pair-links with x; they
are the three points outside the deleted block B. Since the complete
L_x has no further W incidences, these C5 stars are complete. The
complete-C5 lemma and (2) bound their degrees by15. The three P5 points
retain the global degree bound16. Therefore

    D<=3*15+3*16-27=66.                                   (3)

Using (1)--(3) in the same identity now gives

    O>=11+E_3.                                            (4)

## Every outside member has the same two surviving K triples

Fix Q in O. The complement bound22 and NO47 give |D(Q)|=22.
The equality analysis in `P9-disjoint-complement22.md` shows that at
an exact degree16 root the only possibility is

    |K'|=2,
    eleven x-avoiders in D(Q),
    all nine H-block completions and two exceptional completions.

For completeness, the other possible equality case would have six
K triples through one common point. Removing that point gives two
disjoint triangles. The seventh K triple could not meet them both,
contradicting intersection of K. A common-point case with at most5
surviving triples has at most21 members by the guarded estimate16+k.

Each of the nine H blocks already has an x-cone, so its remaining
global triple capacity permits exactly one other completion. Thus the
nine completions just found are globally fixed, and they all belong
to D(Q) for every Q in O. Let C be the set of their exterior completion
centres. If |C|=1, all nine copied H blocks would form another actual
P9 star at one centre a outside {x} union W. These two identical
intersecting cross-tail families violate HP15, since9+9>15. Hence
|C|>=2.

Every centre in C must lie in both surviving K triples: its copied
block lies in W, the K triple avoids W, and the two actual members of
D(Q) must intersect. Two distinct triples meet in at most two points.
Therefore C consists of precisely two points a,b, and both surviving
triples contain {a,b}. Global triple-codegree2 on {x,a,b} means these
are the same two K triples for every Q:

    U={a,b,z_1},         V={a,b,z_2},        z_1!=z_2.       (5)

All points displayed in either triple are distinct as required, and
every Q in O avoids a,b,z_1,z_2. Moreover E_3>=11, since the eleven
x-avoiders of any D(Q) have exact W trace size3. Thus (4) yields

    |O|>=22.                                              (6)

Here O also denotes the actual outside family when writing |O|.

## The remaining five K triples split three-plus-two

Take T in K other than U,V. Since K is intersecting, if T avoided
both a,b it would have to contain z_1,z_2 to meet U and V. Its third
point t would belong to every Q in O: those Q must meet the x-cone
of T because T is not among their two surviving K triples, but they
avoid x,z_1,z_2. This would give d(t)>=|O|>=22, contrary to cap16.

Hence every remaining K triple contains a or b. It cannot contain
both, because U,V already consume both units of triple-codegree on
{x,a,b}. Each contains exactly one of them.

An intersecting SF3 family of seven triples has maximum point degree
at most5. Indeed, degree6 would give two disjoint triangles after
removing that point; an additional triple avoiding the point would
need at least four vertices to cover both. Degree greater than6 is
already forbidden by the SF2 bound. Since U,V each use both a,b,
at most three additional K triples can contain either centre.
The five remaining triples therefore split3+2 between a,b. Rename
a,b if necessary so that a has three additional triples.

## The five-edge graph at the heavier centre

The point-link of a within K has five edges. It is a simple SF2 graph,
so its maximum degree and matching number are both at most2. It
contains the two-edge path

    z_1 -- b -- z_2,

from U,V. Its other three edges are the tails of the three additional
a-triples. Every member of O avoids b,z_1,z_2 and must meet each of
these other edges.

A five-edge SF2 graph is either a five-cycle or a vertex-disjoint
triangle and two-edge path; this follows from its degree and matching
bounds, as in frozen `paper/main.tex:188--204`.

If it is a five-cycle, the given two-edge path is consecutive. The
other three edges form a path z_1-u-v-z_2. Every outside member must
contain u to meet z_1-u (and also v to meet v-z_2), forcing d(u)>=22,
impossible.

If it is a triangle plus a two-edge path, the displayed path is either
inside the triangle or is the entire path component. In the first
case the third triangle edge is z_1z_2, which no outside member can
meet. Thus only the second case remains: the three additional edges
form a triangle T disjoint from {b,z_1,z_2}.

Every Q in O must cover T, so uses at least two of its three points.
The three actual K-cones {x,a} union e, for e an edge of T, already
use six incidences on T and are distinct from all members of O.
Global cap16 therefore gives

    2|O|+6 <= sum_(t in T)d(t) <=3*16=48,
    |O|<=21,

contradicting (6). This closes the degree16 P9 branch.

## Scope and sources

This proof does not assume the eleven copied completions are the only
global triple traces, or that every member outside x is intersecting.
Only the combined trace0/trace1 pool and each actual disjoint complement
are used as intersecting subfamilies. The completion-centre set C is
derived from forced global triple-capacity saturation.

The ordinary source boundary is the three initial notes, H27, the
complete-C5 lemma, and the universal SF2/SF3/cross-star facts they name.
The frozen prior repository is
`work/frontier20261020/prior-art68/repository`, pinned commit
`90c03c79bcf44eb8f61dff1b86091b822cc4cd3c`.
The relevant paper locators are188--204 (five-edge SF2 graph),
206--231 (P9/P10),272--350 (isolation/codegrees),1001--1024 (guarded
cross-star), and1124--1144 (complete-link intersecting bound20).

No old mu42 bootstrap, I7 classification, support restriction,
minimum-degree premise, numerical branch certificate, or global67
conclusion is used or claimed.
