# Independent ordinary check of NO47 at cap16

23 October 2026. Ordinary proof development, not a final audit. No solver,
enumeration or Lean process was used. This independently expands the
proposed singleton7 link argument and its small arithmetic reduction.

**Conclusion.** Conditional on the named prior ordinary inputs and the
new cap16 no-P10 result, every actual member of a size68 SF4 family with
global degree cap16 has neighbourhood at most46.

## Inputs and notation

Use H27, the imported crowding26 and guarded HP15 results, universal
exact-trace/codegree bounds, B4 and isolation, and the universal R16 and
I8/I9/I10 classifications. The ordinary no-P10 theorem is
`D16-P10-ordinary-exclusion.md`. It implies singleton counts at most9.
The earlier cap16 bound N<=47 and the following local facts are proved
in `LOW15-large-singleton-core.md`, with their degree guards explicit:

* A point with exact singleton s_i>=8 has pair row r_i<=6, even with
  exact triple traces present.
* If also r_i>=5, every incident exterior pair edge lies on a single
  triangle T_i, each triangle edge having multiplicity at most2.
* Two such roots sharing a pair category of size at least2 have the
  same triangle.
* If all roots have s_i>=8 and r_i>=5, the common-triangle/HP15 argument
  is contradictory.
* An exact triple member Q_l=(R minus l) union {u}, when all three
  other roots have singleton count at least8, forces r_l<=4.

Let R be a hypothetical actual member with N(R)=47. Put s_i for its
four exact singletons, p_ij for pairs, t_i for the triple omitting i,
and S=sum s_i, T=sum t_i, r_i=sum_(j!=i)p_ij. Define degree deficits
delta_i=16-d(i)>=0. The exact identities are

    sum d(i)=96-S+T,
    sum delta_i=S-32-T,
    r_i=15-delta_i-s_i-T+t_i.                              (1)

Crowding gives S<=34, so S>=32+T and T<=2. Singleton cap9 and the
largest-three bound26 give precisely these sorted possibilities:

    S32: (6,8,9,9), (7,7,9,9), (7,8,8,9), (8,8,8,8);
    S33: (7,8,9,9), (8,8,8,9);
    S34: (8,8,9,9).

This list follows just by distributing a total of32--34 among four
integers at most9 and checking the largest-three sum. It is not a
geometric realization catalogue.

## Eliminate triple traces

If T=2, then S=34 and all delta_i=0. Every root is large. At an omitted
root l with t_l=1, (1) gives r_l=14-s_l>=5, contrary to the literal
triple-member bound4.

If T=1,S=34, then sum delta_i=1 and again every root is large. At the
unique omitted root l, r_l=15-delta_l-s_l>=5, the same contradiction.

If T=1,S=33, all delta_i=0. A root with singleton8 has row6+t_i, so
cannot be the omitted root because of the row bound6. In the pattern
(8,8,8,9), the omitted root must therefore have singleton9; it has
row6 and the other three roots are large, contrary to the bound4.

For (7,8,9,9), the omitted root cannot be the singleton7 root, since
the other three roots are large and its row would be8. It must be a
singleton9 root l, with r_l=6. Let u be the exterior point of Q_l.
The row at l lies on a triangle T_l. B4 at each of its two other large
partners forces every edge in those categories to contain u. At least
one such category is nonempty because the one small partner category
has at most3 members, so u belongs to T_l.

Every edge in the small-partner category lies on T_l as well. At most
one of its distinct edges avoids u. Therefore at least r_l-1=5 pair
members of the row use u. But the two edges of T_l through u have
multiplicity at most2 each, permitting at most4. This contradiction
eliminates the last T=1 case. Hence T=0.

## Reduce the zero-triple cases to (7,7,9,9)

Now each singleton8 root requires delta_i>=1, by (1) and r_i<=6.
At S32 all deficits are zero, so the only possible pattern is
(7,7,9,9). At S33 the sole possible pattern is (7,8,9,9), with its
one deficit at the singleton8 root. The pair rows are then (8,6,6,6).
At S34 the pattern is (8,8,9,9); each singleton8 root consumes one
of the two deficits and all four pair rows are6. The latter is excluded
by the common-triangle/HP15 theorem.

For (7,8,9,9), denote the singleton7 root by l. The three large roots
have row6 and local triangles. Their mutual pair counts total
(18-8)/2=5, while their counts to l total8 and are each at most3.
Thus the latter counts are (2,3,3), so the degrees within the weighted
triangle of large roots are (4,3,3). Its edge weights are (2,2,1).
The two edges of weight2 connect all three large roots, identifying
their triangles. Every category at l is supported on this same
triangle, and each of its three exterior edges has multiplicity at
most2 by triple codegree. This gives r_l<=6, contrary to r_l=8.

We are left with precisely

    s=(7,7,9,9), T=0, all d(i)=16, r=(8,8,6,6).            (2)

## The singleton7 complete-link obstruction

Choose a singleton7 root l. Its complete triple link L=L_l has size16.
Let A=R minus l, an actual triple of L. Exactly seven members of L
are disjoint from A. Every point j of A has L-degree

    d_L(j)=d_F(l,j)=1+p_lj<=4,                             (3)

because T=0. The following universal link cases all contradict these
two facts.

**R16.** If rho(L)<=7, the universal R16 classification applies.
Every displayed R16 triple contains a hub of degree6; its other point
degrees are4. Hence A contains a degree6 point, contrary to (3).
This invokes the actual R16 theorem, not an assertion that every
sixteen-triple link separates.

**A B4 partition with a P-type component.** Otherwise some actual
triple has at least8 disjoint triples. B4 partitions L into two
intersecting families of sizes10+6,9+7 or8+8. No-P10 removes10+6.
If either side of the remaining partition is P-type, isolation makes
the supports disjoint. A possible deleted P10 block cannot be on the
opposite side: it is in the same neighbourhood/disjointness class as
the P-type side relative to the chosen B4 anchor. This is the explicit
support argument in `C5-internal-compatibility.md`.

In the9+7 case, A must lie in the P9 part, since an A in the opposite
part would be disjoint from all9 P9 triples. Every P9 block contains
a degree5 point: its three degree4 points form exactly its omitted
P10 block, which is absent. This contradicts (3). In a separated8+8
case, every member has exactly8 disjoint members, contrary to A's7.

**Two Q8 parts.** It remains possible that both B4 parts are Q8,
with shared leaves. The far Q8's core avoids the whole near support:
by isolation a near triple touching that core would be a hub plus both
far leaves, hence would also avoid the chosen B4 anchor and be far.
For the reciprocal direction, suppose a far triple touches the near
Q8 core. Isolation of the near Q8 makes it a near hub plus both near
leaves, wholly inside the near support. But every far Q8 triple contains
a point of its own core, which was just shown disjoint from that support.
This is impossible. Thus both cores avoid the entire opposite support;
only leaves may overlap.

If A is a core triple of its Q8, all8 triples of the opposite Q8
avoid A, contradicting its disjoint count7. If A is a leaf triple,
it contains both hubs, each already of degree5 in its own Q8. This
contradicts (3). This case does not assume disjoint full Q8 supports.

All cases are exhausted, so (2) is impossible. Therefore N47 is
excluded and every actual neighbourhood has size at most46.

## Precise consequence and remaining boundary

This check validates the proposed NO47 step conditional on the named
ordinary/imported facts. Combined with `P9-disjoint-complement22.md`,
it gives |D(Q)|>=22 but not a strict contradiction with its upper
bound22. To obtain global no-P9 from that lemma alone one still needs
NO46, or a proof excluding its equality configurations.

The frozen prior sources are under
`work/frontier20261020/prior-art68/repository`:
`paper/main.tex:206--231,272--331` for the models, classification,
isolation and B4; `443--462` for R16; and `968--1024` for crowding and
guarded cross-star. The complete-C5 note and
`LOW15-large-singleton-core.md` give the separately stated local
lemmas used above. No support cutoff, old mu42/minimum-degree premise,
I7 classification, or new finite certificate is used.
