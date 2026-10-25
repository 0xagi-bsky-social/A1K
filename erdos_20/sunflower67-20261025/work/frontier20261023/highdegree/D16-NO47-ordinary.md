# Cap16: every actual neighbourhood has size at most46

23 October 2026. Ordinary research development. No new numerical search,
finite certificate replay, support cutoff, final review, or Lean claim.

## Dependency order and imported boundary

Let F be a finite simple SF4 family of size68 with maximum point degree
at most16. Empty-core sunflowers are forbidden. We use H27 (hence mu>=41),
exact trace bounds10/3/1, global triple codegree2, B4, I8/I9/I10
classification and isolation, universal R16 classification, and the
previously replayed crowding26 and HP15 imports. Their prior provenance is
recorded in `PRIOR_DELTA18_UNLOCK.md` and `D17-I7-classification-route.md`.
The R16 import is the universal theorem in the frozen paper, not an
assumption that an arbitrary low-degree link has small support.

`LOW15-large-singleton-core.md` first proves N<=47 under cap16, without
excluding P10. `D16-P10-ordinary-exclusion.md` then excludes every P10
subfamily of every point-link under cap16. Consequently each exact
singleton count is at most9. Both statements precede this proof.

For an actual anchor R={0,1,2,3}, write s_i,p_ij,t_i for exact singleton,
pair, and triple counts (t_i omits i). Put S=sum s_i, T=sum t_i and
r_i=sum_(j!=i) p_ij. Then

    d(i)=1+s_i+r_i+T-t_i,
    sum_(i in R) d(i)=2N(R)+2-S+T.

The following ordinary local facts were proved in
`LOW15-large-singleton-core.md`:

* s_i>=8 implies r_i<=6, even when T>0.
* s_i>=8 and r_i>=5 put all incident exterior pair residues on one
  triangle, with each edge used at most twice.
* If all four s_i>=8 and all four r_i>=5, the common-triangle and HP15
  argument is contradictory (in particular when T=0).
* If t_l=1 and all other singleton counts are at least8, then r_l<=4.

We also use this immediate weighted version of the last fact. Suppose
s_l>=8,r_l>=5,t_l=1, and at least one positive category lj has s_j>=8.
Write the actual triple member as (R minus l) union {z}. B4 at every
such high neighbour forces z into every edge of E_lj. In particular z
belongs to l's triangle. A category of p edges on that triangle contains
z at least max(p-1,0) times. Since z has total pair-edge multiplicity
at most4 on the triangle,

    sum_(j high) p_lj + sum_(j low) max(p_lj-1,0) <=4.       (W)

This is a necessary inequality on actual edges; it assumes no finite
bound on the exterior support.

## Arithmetic reduction of N47

Suppose N(R)=47. Since sum d(i)<=64, we have S>=32+T. Crowding gives
S<=34, so T<=2. Below the sorted singleton patterns are exhaustive:
all entries are at most9, and their largest three have sum at most26.
Write delta_i=16-d(i)>=0. Then

    r_i=15-s_i-T+t_i-delta_i,
    sum delta_i=S-T-32.

For T=0:

* S32 has patterns (6,8,9,9), (7,7,9,9), (7,8,8,9), (8,8,8,8).
  All degrees equal16. Every pattern except (7,7,9,9) has a singleton8
  root with pair row7, violating the local row bound. The exceptional
  pattern has pair rows (8,8,6,6).
* S33 has patterns (7,8,9,9) and (8,8,8,9), with total deficit1.
  The latter has three singleton8 roots and cannot lower all their
  nominal rows7. In the former the only possible deficit is at the
  singleton8 root, leaving rows (8,6,6,6). The three high roots each
  have row6. Each must have a category of size at least2 to another
  high root, because otherwise its row is at most1+1+3=5. Thus the
  graph of such categories on the three high roots is connected.
  Their triangles coincide. Every category at the low root belongs
  to this same triangle; its row8 contradicts the total edge capacity6.
* S34 has only (8,8,9,9). Total deficit2 must lower both nominal
  singleton8 rows7, leaving all four pair rows6. The common-triangle
  obstruction applies.

For T=1:

* S33 has total deficit0. If the pattern is (8,8,8,9), omitting a
  singleton8 gives row7; omitting the singleton9 gives row6, whereas
  the literal triple-star bound gives row<=4. If the pattern is
  (7,8,9,9), omitting7 gives row8 and the same triple-star contradiction;
  omitting8 gives row7. Omitting9 gives row6. At least one high
  neighbour is positive because the single low category has size at
  most3. Inequality (W) then has left side at least r_l-1=5, a
  contradiction.
* S34 has pattern (8,8,9,9) and total deficit1. The omitted root has
  row at least5, contradicting the triple-star bound4.

For T=2, necessarily S34 and all degrees16. Every omitted root has
row5 or6, again contradicting the triple-star bound4. Thus only the
T0 pattern (7,7,9,9), all degrees16, remains.

## The exceptional pattern cannot have a complete link

Choose a singleton7 root l. Its complete triple link L=L_l has size16.
The actual triple A=R minus l has exactly seven disjoint members in L,
namely the exact-l singleton family. Since T=0, each point j in A has
complete L-degree

    d_L(j)=d_F(l,j)=1+p_lj<=4.                              (1)

Put rho(L)=max_(B in L) |D_L(B)|. If rho(L)<=7, the universal R16
classification applies. Its four hubs have degree6, and every actual
triple contains a hub. This contradicts (1) for A.

If rho(L)>=8, choose a witnessing actual triple and apply B4. The
complete link partitions into two intersecting families. Their sizes
sum to16 and each is at most10. Neither can contain ten triples,
because P10 has already been excluded. Thus their sizes are 9+7 or8+8.

In the 9+7 case, P9 isolation makes the two supports disjoint. Its
missing block cannot be in the other component: that would give a
P10 in L. Since A has seven disjoint triples, A lies in the P9 side.
Every actual P9 block contains a degree5 point: the three degree4
points are exactly the omitted P10 block, which is absent. Its degree
in L is still5 by support separation, contradicting (1).

In the 8+8 case, if either side is P8, P8 isolation separates the
supports. A deleted block cannot be in the other side. If P8 is the far side,
its support avoids the witnessing anchor, so a deleted block would
also be far. If P8 is the near side, it contains that anchor, and
every deleted P10 block meets it, so a deleted block cannot be far.
Every actual triple then has exactly eight disjoint triples, contrary
to |D_L(A)|=7.

It remains Q8+Q8. Each five-point core avoids the entire opposite
support; shared leaves are permitted. For clarity this holds in both
directions: B4 first isolates the far core. An opposite-core exception
in the far side would be a hub-plus-both-leaves triple lying entirely
on the opposite support, but every far Q8 triple contains a point of
its isolated core. Thus the reciprocal exception is impossible.
A core-only Q8 triple is disjoint from all eight opposite triples. A
leaf triple contains the two hubs, each of degree5 within its own Q8.
Consequently an A with only seven disjoint triples must be a leaf
triple, contradicting (1) again.

All possibilities are excluded. Combining with the preliminary N<=47
bound proves N(R)<=46 for every actual member R under global cap16.
This is a conditional ordinary theorem using the stated imported
classifications; it is not a claim that the whole cap16 branch is closed.
