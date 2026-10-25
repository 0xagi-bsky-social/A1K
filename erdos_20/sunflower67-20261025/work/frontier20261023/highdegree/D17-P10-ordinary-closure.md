# Ordinary closure of the degree17 P10 branch

23 October 2026. Ordinary proof development, not a final audit or Lean
formalization. No solver, catalogue construction, numerical model, or
certificate replay was executed for this note. The existing twelve
nonempty-internal replay results were read as data. Exterior support
remains unrestricted throughout.

**Conclusion.** For a simple three-sunflower-free four-uniform family of
68 members, a degree17 point whose link contains P10 cannot have an empty
internal family on that P10 support. Together with the existing twelve
nonempty-internal exclusions at global degree cap17, this closes the
entire degree17 P10 branch. The ordinary empty-internal argument requires
no classification of the opposite intersecting seven-triple family.

## Premises and the internal-exclusion boundary

Let F have exactly68 members and no three distinct members with equal
pairwise intersections, including empty core. Let x have degree17, and
suppose its link contains P10 on a six-point support Y. Isolation gives
the complete link decomposition

    L_x = P10(Y) union K,

where every triple of K avoids Y and |K|=7. The seven triples need not be
classified or assigned a finite ambient support in the argument below.
Assume for now that no actual member of F is a four-subset of Y.

The imported mathematical ingredients are H27, the universal global
pair/triple codegree bounds6/2, P10 isolation and elementary block
incidences, and the complete-C5 lemma in
`C5-internal-compatibility.md`. Its R16 and shared-Q8-leaf cases are part
of that explicit ordinary source boundary. H27 gives mu>=41 since the
members disjoint from any actual Q form an intersecting family.

To remove the empty-internal assumption at global cap17, use the separate
complete internal-orbit bridge `D17-P10-internals.md` and the twelve
receipts `degree17/P10_001.json` through `P10_012.json`. The file
`degree17-replay/P10-nonempty-summary.json`, read for this note, records
count12 and all_pass=true. Its stated assurance is shared-model exact
integer replay, not independent model reconstruction or Lean. This note
does not strengthen that assurance, redo the replay, or import the old
mu42 refutations. The initial bridge's historical pending-replay wording
is superseded in status by the separate replay summary.

The ordinary proof below closes the unique empty assignment directly.
It can therefore replace a further division of that assignment according
to the possible I7 shapes and their numerical certificates.

## Residual trace counts and the strengthened incidence bound

Partition the51 actual members avoiding x by the size of their exact
intersection with Y. Write O,H,P,E for trace sizes0,1,2,3, respectively.
There is no size4 class by the empty-internal assumption. Thus

    O+H+P+E=51,
    D:=sum_(Q avoids x)|Q intersect Y|=H+2P+3E.             (1)

For each y in Y, the complete pair-link of x,y is the prescribed C5.
Completeness follows because all other triples of L_x avoid Y. The
complete-C5 lemma implies d(y)<=15 when no internal member on Y is
present: at degree at least16 the component containing the five C5
cones would require an additional internal cycle-cover triple.
The prescribed ten x-cones use30 incidences on Y, so

    D=sum_(y in Y)d(y)-30 <=6*15-30=60.                    (2)

All members in the trace0 and trace1 classes together form an
intersecting family. If two were disjoint, their combined Y trace
would have size at most2. Some P10 block avoids that trace; its actual
x-cone would then be disjoint from both, a forbidden empty-core
sunflower. H27 gives

    O+H<=27,           P+E>=24.                           (3)

Only this combined trace0/trace1 family is asserted to be intersecting.
There is no assertion that every member avoiding x is intersecting.

## The universal C5 pair-pool bound

Fix y in Y, and let b_y count residual members whose exact Y trace is
a pair containing y. Write such a member as

    {y,j} union e,

where j is another point of Y and e is a two-set outside Y union {x}.
The family of distinct exterior edges e is pairwise intersecting:

* If two disjoint edges occur at different partners j,k, the C5
  point-link at y has an edge avoiding both j and k. Its actual cone
  meets each residual member exactly at y, as do the two residual
  members with each other. This is a singleton-core sunflower.
* If the two partners coincide at j, use a prescribed cone containing
  x,y,j. Its intersections with the residuals, and their mutual
  intersection, are all {y,j}, again a sunflower.

The first witness exists because C5 has no two-vertex cover; the second
exists because every P10 pair occurs in two blocks. Distinct members
with the same exterior edge are retained with their actual multiplicity.

An intersecting simple graph is a star or a triangle. In the star case,
all b_y actual members contain its centre z along with y, so the global
pair codegree gives b_y<=6. In the triangle case each of its three edges
e has multiplicity at most2, by the codegree bound on the triple
{y} union e, again giving b_y<=6. The empty and single-edge cases are
included in the star alternative.

Every residual pair trace is counted at its two Y endpoints. Hence

    2P=sum_(y in Y)b_y<=6*6=36,           P<=18.            (4)

This pair-pool argument uses neither the empty-internal assumption nor
H27, mu41, the size of K, a support cutoff, or a classification of K.
It is exactly the universal argument in the frozen
`companion/upstream/D18_P10/PROOF.md:62--97`, especially lines69--78.
It applies to the whole C5 pair pool; it must not be transferred to
the whole pair pool of a P5 point without the separate cover restriction.

Combining (3),(4),

    E>=6.                                                 (5)

## The ten-cone average

Let W be the sum, over the ten prescribed x-cones A, of the number of
residual members meeting A. Every member containing x meets every
such cone. Since d(x)=17 and every actual cone has neighbourhood at
least41,

    W=sum_A (|N[A]|-17)>=10*(41-17)=240.                   (6)

A singleton Y trace meets5 P10 blocks, a pair meets8, and a triple
meets at most10. The empty trace meets none. Therefore

    W<=5H+8P+10E
      =5D-2P-5E
      =5D-2(P+E)-3E
      <=300-48-18=234,                                    (7)

by (2),(3),(5). Equations (6),(7) contradict each other. This proves
the ordinary empty-internal closure.

All nonblock triple traces are permitted by (7); they meet only9
blocks and thus would strengthen the inequality. No equality or
realizability claim about a projected numerical point is needed.

## A slightly more general statement

The same proof works whenever x has degree m<=17, P10 is isolated in
its complete link, and the Y-internal family is empty, without a global
degree17 hypothesis for the ordinary step. With |F|=68 it gives

    P+E>=41-m,        E>=23-m,
    410-10m<=W<=300-2*(41-m)-3*(23-m)=149+5m,

hence261<=15m, contrary to m<=17. The support-point cap15 in (2) comes
from the universal complete-C5 lemma, not the assumed global cap.

The global cap17 remains a hypothesis of the existing twelve
nonempty-internal certificates when they are used to close the entire
degree17 branch. No claim is made here that the other degree17
P9-plus-I8 branch has been excluded, or that the global extremal bound
has been proved.

## Source boundary

Frozen prior repository:
`work/frontier20261020/prior-art68/repository`, pinned commit
`90c03c79bcf44eb8f61dff1b86091b822cc4cd3c`.

* `paper/main.tex:188--231,272--350`: canonical intersecting triple
  families, isolation and universal codegree bounds.
* `paper/main.tex:443--462,612--636`: R16 and high-link structure used
  by the separate complete-C5 lemma.
* `companion/upstream/D18_P10/PROOF.md:62--97`: the universal pair-pool
  argument, explicitly independent of mu42 and ambient support limits.
* `C5-internal-compatibility.md`: the complete-C5 support-point bound,
  including R16 and Q8 exceptions.
* `D17-P10-internals.md` and
  `degree17-replay/P10-nonempty-summary.json`: the separate necessary-model
  bridge and completed exact replay status of the twelve nonempty orbits.

The ordinary empty-internal proof uses no crowding26, HP15, minimum
used degree, I7 enumeration, or additional numerical certificate.
