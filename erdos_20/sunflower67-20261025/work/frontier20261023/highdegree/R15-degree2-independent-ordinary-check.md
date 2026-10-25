# Independent check of the size15 rho6 degree-two reduction

24 October 2026. Ordinary proof development and bounded exact validation,
not a final research audit or Lean theorem. The checker below imports
neither producer. No LP, numerical solver, or Lean process was run.

## Result and precise boundary

The arbitrary-support reduction in
`R15-rho6-degree2-support-reduction.md` is sound under its stated SF3,
size15 and rho<=6 hypotheses. Both degree-two motifs are excluded by
the independently reconstructed finite obstructions. Consequently every
used point has degree at least3, there are at most11 used points, and
some point has degree5 or6. The resulting three normalized point-link
domains are two triangles, C5, and a triangle plus a two-edge path.

This note does not check the later complete fifteen-member searches on
those eleven-point domains. Their exhaustion and independent proof-tree
verification remain separate evidence. The frozen reduction note's final
paragraph records their earlier pending status; that timestamped status
does not affect the mathematical support argument checked here.

## Ordinary motifs and why their normalization covers arbitrary support

Minimum used degree at least2 follows from the elementary argument in
`LOW15-R15-rho6-partial-status.md`. A degree-one root x in xyz cannot
have a degree-six neighbour. The neighbourhood bound9 forces y,z both
degree5 and all pair codegrees1, but the five-edge point-link would put
x at a path leaf and the other point at its middle of codegree2.

Suppose x has degree2 and a degree-six neighbour a. The two-triangle
a-link forces xab,xac,abc. Since d(xb)=d(xc)=1, neither b nor c can
have degree6; the exact neighbourhood formula N(xab)=4+d(b)>=9 then
forces both degrees5. Their five-edge links contain the two-edge paths
x-a-c and x-a-b, respectively, and their other components are triangles.
The remaining component in the a-link is a triangle as well. Thus the
three-triangle, twelve-triple motif in the reduction is forced.
The four points x,a,b,c are saturated at degrees2,6,5,5: b,c cannot
increase to6 because their codegree-one pairs with x are permanent.

Fix the first triad T=456. The stabilizer of this set makes the second
triad D depend only on its overlap k=0,1,2,3, with the common points
chosen first and all other points new. For each such D, the third
triad E is specified by an arbitrary old subset and a set of fresh
points. The fresh points can be renamed consecutively. There are

    [binom(6,3)+binom(6,2)+6+1]
  + [binom(5,3)+binom(5,2)+5+1]
  + [binom(4,3)+binom(4,2)+4+1]
  + [binom(3,3)+binom(3,2)+3+1]
    =42+26+15+8=91

normalized motifs. This is a normalization of three prescribed triads,
not a global support cutoff. For one further triple, at most three
new labels are needed. Every possible such triple avoiding the four
saturated points is forbidden by a literal pair of motif members.

If x has degree2 and no degree-six neighbour, take xyz. A degree4
neighbour would force the other degree5 and all three codegrees1;
the same five-edge point-link obstruction rules this out. Hence both
neighbours have degree5. If one pair involving x had codegree2, the
opposite degree5 point-link would also force yz to have codegree2,
giving neighbourhood at most8. Thus d(xy)=d(xz)=1 and d(yz)=2.
The shared second yz member fixes the same w in both path components.
The two other components are triads D,E outside x,y,z,w; the second
x-member is xuv, with u,v outside x,y,z but possibly including w.
This gives nine distinct mandatory triples. The points x,y,z are
saturated, so all six further triples must avoid them.

Fix D=456 and normalize E by its overlap with D. The allowed old set
for uv includes w and has size7,6,5,4 respectively. Choosing zero, one
or two fresh labels gives

    [binom(7,2)+7+1]+[binom(6,2)+6+1]
  + [binom(5,2)+5+1]+[binom(4,2)+4+1]
    =29+22+16+11=78

motifs. This includes every possible coincidence of u,v with the two
triads or w. The no-degree6 condition at u,v need not be imposed in
the finite search: omitting it only enlarges the candidate domain.

## The whole-completion exterior bound

For each surviving nine-triple motif, test a single future triple on
the old support plus three fresh points. The independent check confirms
that every admitted triple with a fresh point has exactly one; its
other two points form an old pair P. Let c(P) be the number of motif
triples containing P. Across all admitted exterior pair types, the sum
of remaining capacities 2-c(P) is at most3.

Every future triple using any point outside the fixed motif consumes
one unit at exactly one of these old pairs. It cannot use two exterior
points, by the literal one-triple obstruction already checked. Thus
an entire completion has at most three triples involving new points,
and hence at most three distinct new points. This proves that the
checked completion universe covers arbitrary ambient support. It is
stronger than a bound of three new labels per separately tested triple.

The independent budget histogram over the18 surviving motifs is
0 for3 motifs,1 for7,2 for6, and3 for2. Every projected pair capacity
was recomputed directly from the nine actual triples and compared with
the saved receipt, rather than trusting the reported total.

## Independent exact check

`recheck_R15_degree2_support.py`, SHA256
`72482f0ce7cbb4990dba7df55958c41693ae85d5d7b332c062c881181ae0accd`,
ran with `timeout 10s` and completed in about0.143 seconds. Its output
is `R15-degree2-independent-check.json`.

It reconstructs normalized motifs by choosing the old subset size and
adding the required canonical fresh prefix; it does not import either
producer's generation code. It checks exact equality of reconstructed
and saved motif sets, no duplicate rows, all actual member identities,
all literal rejection witnesses, and complete coverage of every next-
triple domain. It separately recomputes the permitted triples and the
whole-completion exterior budgets.

For the second motif it does not replay the producer's increasing-index
DFS or trust its319-node count. It enumerates all six-element subsets
of the permitted-next-triple set. There are74761 subsets in total.
Every one contains two selected triples and a fixed motif triple that
form a sunflower. Thus no later rho or capacity pruning is needed for
these independently checked terminal exclusions.

The exact check also verifies1580 saved three-member sunflower witnesses,
nine saved seven-disjoint-member witnesses, and364 pair witnesses
for the first motif's proposed thirteenth triples. The91 motifs reduce
to6 admissible twelve-member motifs, all with no next triple; the78
motifs reduce to18 admissible nine-member motifs, all with no six-triple
completion. Source and receipt hashes are recorded in the new JSON.

## Eleven-point support and complete root cases

Let I count unordered intersecting pairs of triples and r(v) the number
of codegree-two neighbours of v. Since rho<=6 and |L|=15,

    I>=15*8/2=60,
    I=sum_v [binom(d(v),2)-r(v)/2],   sum_v d(v)=45.

The second identity subtracts the extra count for pairs of triples
intersecting in two points. For d=3,4,5,6, SF2 point-links give minimum
r=1,2,4,6, so the summands are at most5/2,5,8,12. Each is bounded by
19*d/6-7. Therefore60<=285/2-7*n, giving n<=11. With maximum degree
at most4, each summand is at most5*d/4, giving I<=225/4<60; hence a
degree5 or6 point exists.

A degree-six SF2 point-link is two disjoint triangles; a degree-five
one is C5 or a triangle plus a two-edge path. These are complete
point-links, not contained subfamilies. Padding their proved at-most11
support to eleven labels is therefore legitimate for the subsequent
finite searches. No size16 exhaustion is being reused to infer a
size15 conclusion.
