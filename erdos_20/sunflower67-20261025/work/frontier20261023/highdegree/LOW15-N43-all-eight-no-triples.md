# Cap15: exclude N43 with four singleton8 pools and no triple traces

24 October 2026. Ordinary proof development, saved in the existing Oct23
directory. This closes one N43 subcase, with arbitrary exterior support.
No solver, numerical census, or Lean compilation is used. It does not
claim exclusion of every N43 profile or a global67 theorem.

## Statement and imported facts

Let F be finite, simple, four-uniform and free of three-member sunflowers,
including empty core. Suppose |F|=68 and every point degree is at most15.
Use H27, so every actual member Q has neighbourhood size N(Q)>=41.
Use the universal B4 lemma, I8 classification and isolation, and HP15 in
their stated domain mu>=41 and Delta<=18. HP15 bounds the sum of two
intersecting SF3 tail families by15 when they have distinct centres outside
both supports and are cross-intersecting. These imports and their evidence
boundary are recorded in `PRIOR_DELTA18_UNLOCK.md`.

Then there is no actual member R with

    N(R)=43, all four exact singleton counts equal8,
    and all four exact triple counts equal0.

The proof uses the ordinary local triangle and Q8-leaf matching arguments
in `LOW15-large-singleton-core.md`. It does not need the classification of
size15 links, the global no-P9 theorem, or a classification of cross-pairs
of Q8 families. In particular, possible shared leaves are retained until
they are excluded or explicitly used below.

Write R={0,1,2,3}. For each i let D_i be the eight exterior triples in
the exact singleton pool at i; their lifts {i} union U are actual members
of F. All D_i avoid R. Let K_i be the remaining triples of the complete
i-link. B4 makes K_i intersecting. For i!=j let E_ij be the family of
exterior two-sets e for which {i,j} union e is actual, and put

    p_ij=|E_ij|, r_i=sum_(j!=i) p_ij.

Every p_ij<=3. Each E_ij is an intersecting graph; when it has three
edges, it is a triangle, since a three-edge star would violate global
triple codegree2. Because the exact triple counts vanish,

    sum_(i<j) p_ij=10, sum_i r_i=20, d(i)=9+r_i<=15.

The far family D_i is either P8 or Q8. P8's entire support is disjoint
from K_i's support. For Q8, only its five-point core is initially known
to avoid K_i's support. In notation used later, a Q8 family has distinct
hubs h,h', distinct triad points u,v,w and two distinct leaves l,l', all
seven points distinct, and consists of

    {h+e,h'+e : e in binom({u,v,w},2)}
      union {{h,h',l},{h,h',l'}}.

If a Q8 leaf t occurs in K_i, its leaf triple {h,h',t} and two near
triples through t whose residual pairs are disjoint would form an SF3
sunflower with core {t}. The hubs avoid the near support by core isolation,
so this is a literal forbidden triple. Consequently a matching of size2
in the near point-link at t excludes t as a far Q8 leaf.

## Reduction to rows (4,4,6,6)

Call a root good when r_i>=5. The local triangle lemma gives an exterior
triangle T_i carrying every incident E_ij, with each triangle edge used
in at most two categories. It also gives D_i disjoint from R union T_i,
including its possible Q8 leaves: every point of T_i has at least three
edges in its near bipartite point-link, of maximum degree2, and hence
has a matching of size2. A shared category of size at least2 identifies
the two good roots' triangles.

If all four roots are good, the common-triangle theorem in the cited
note applies. It makes the four triangles agree and uses an actual pair
member as a witness forcing two size8 far families to cross-intersect,
contrary to HP15.

If exactly three roots are good, let the remaining row be q<=4. Since
the other three rows are at most6 and the total is20, q>=2. The sum of
the pair counts among those three good roots is10-q>=6. The graph of
categories of size at least2 on them is connected: if disconnected,
at most one category has size at least2 and the pair sum is at most
3+1+1=5. Their triangles therefore agree, say T. The positive row q
provides an actual member {l,j} union e with e in T and j good. The
complementary two roots are good and their far tails avoid R union T.
Two disjoint tails from those pools, lifted at their centres, would be
disjoint from this member and from each other. They are thus forced to
cross-intersect, again contradicting HP15.

At most one good root gives row sum at most6+4+4+4=18. With exactly
two good roots, the only way to sum to20 is (4,4,6,6). Label the low
roots0,1 and the good roots2,3. In particular d(0)=d(1)=13.

Put a0=p01 and b0=p23. The row sums give

    b0-a0=2, p02=p13=u, p03=p12=v, u+v=4-a0.

Thus (a0,b0) is (1,3) or (0,2). Roots2,3 have a common exterior triangle
T because p23>=2. Their rows are6, so every edge of T occurs exactly
twice among the three incident categories at each of these roots.
Both D_2,D_3 avoid R union T.

In all the cases below, the low-root near support uses all of T. Hence
the five-point core of any low-root Q8 also avoids R union T, and a
low-root P8 avoids R union T entirely. Only Q8 leaves can remain on T.

## The case p01=1 and p23=3

Here E23 is the full triangle T. At root2, E02 and E12 partition the
three triangle edges: each must occur once more beyond its occurrence
in E23. Let e be the sole edge of E01. Intersection of K_0 makes e
meet every edge of E02, and intersection of K_1 makes e meet every
edge of E12. Thus e meets all three edges of T and is itself an edge
of T. This remains true if one of E02,E12 is empty.

The actual member {0,1} union e avoids the centres2,3 and all their far
tails. It forces D_2,D_3 to cross-intersect, contradicting 8+8>15.

## The case p01=0 and p23=2: unequal cross counts

Now u+v=4, so after swapping2,3 the cross counts are (1,3) or (2,2).
The two edges E23 form a path on T. Let f be the missing triangle edge.
The multiplicity2 statement at each good root says that f occurs twice
across its other two categories, and each edge of E23 occurs once there.

For (u,v)=(1,3), this forces

    E02=E13={f}, E03=E12=binom(T,2).

At each endpoint t of f, the near point-link at root0 has three edges:
one from partner2 and two from partner3. It is bipartite with parts
{2,3} and T minus t and has maximum degree2; it has a matching of size2.
Thus D_0 has no Q8 leaf at either endpoint of f. Its only possible
point on T is the third point, so every D_0 tail avoids f. The actual
member {1,2} union f exists in E12. It avoids D_0 and D_3 and their
centres0,3, forcing those two size8 families to cross-intersect. HP15
again gives a contradiction.

## Equal cross counts: the only possible leaf geometry

Suppose (u,v)=(2,2). E02,E12 are the two paths consisting of f together
with one respective edge of E23; E03,E13 have the same property.

If E02 and E03 differ, root0 has the two different paths sharing f.
At either endpoint of f its near point-link has three edges and thus
a matching of size2. At the third triangle point its two near edges
have different partners2,3 and different other triangle endpoints,
so they are disjoint. Consequently D_0 avoids all of T. Any actual
member in E12 then witnesses cross-intersection of D_0 with D_3,
contrary to HP15.

Therefore E02=E03, and E12=E13 is the other path. Name the distinct
triangle points a,b,c so that

    T={a,b,c}, E02=E03={ab,ac},
    E12=E13={ab,bc}, E23={ac,bc}.                 (1)

These letters are exterior to R. At root0, the near point-link at a
is the four-edge bipartite graph {2b,2c,3b,3c}, so a cannot be a far
Q8 leaf. Thus the only possible D_0 points on T are leaves b,c. At
root1 the corresponding matching argument excludes b, leaving only
possible leaves a,c.

If D_0 has no leaf b (including the possibility that D_0 is P8), it
avoids ab. The actual member {1,3,a,b}, supplied by E13, then avoids
D_0 and D_2 and their centres0,2, giving the usual HP15 contradiction.
Thus D_0 must be Q8 with b as one leaf. Similarly the actual member
{0,3,a,b} shows that D_1 must be Q8 with a as one leaf.

Write H_0,H_1 for their respective hub pairs, U_0,U_1 for their triads,
and C_0,C_1 for their six core-only triples:

    C_i={h+e : h in H_i, e in binom(U_i,2)}.

Each five-point core H_i union U_i avoids R union T. This follows from
isolation and (1), whose near support contains all of R minus i and T.
Within each Q8, its hub pair and triad are disjoint; no disjointness
between the two cores is presumed. The second leaves are unrestricted
except by the Q8 definition and the already established matching facts.

## Derive the cross-core geometry without assuming a classification

First C_0,C_1 are cross-intersecting. If X in C_0 and Y in C_1 were
disjoint, their lifts at0,1 and the actual member {2,3,a,c} would be
three pairwise disjoint members: the cores avoid R union T.

Next H_0 is a two-point cover of C_1. For otherwise a core triple Y
in C_1 avoiding H_0 also avoids b, since its whole core avoids T.
The actual leaf member {0} union H_0 union {b}, the member {1} union Y,
and {2,3,a,c} would be pairwise disjoint. Similarly H_1 two-covers C_0,
using the mandatory leaf a and the witness {2,3,b,c}.

For a six-triple core C(H,U), |H|=2 and |U|=3, its two-point covers
are exactly H itself and the three two-subsets of U. Indeed, a pair
with no hub must cover the triangle on U, and hence must be a two-subset
of U. A pair with exactly one hub leaves the three triples at the
other hub to be covered by its one remaining point, which is impossible.
A cover with two hubs is H. This also excludes points outside H union U.

Applying this fact in both directions, either H_0=H_1, or

    H_0 is a two-subset of U_1 and
    H_1 is a two-subset of U_0.                    (2)

If H_0=H_1, every leaf tail of either family meets every tail of the
other in a common hub, and the core tails already cross-intersect.
Hence the full D_0,D_1 cross-intersect, violating HP15. Therefore (2)
holds with H_0,H_1 disjoint, since H_0 avoids U_0 and H_1 avoids U_1.

Write

    U_0=H_1 union {w_0}, U_1=H_0 union {w_1}.

Both w_0,w_1 avoid H_0 union H_1, by the within-core disjointness
conditions, and both avoid R union T. If w_0!=w_1, choose h in H_0,
k in H_1 and let h',k' be their other hub partners. The core triples

    {h,k',w_0} in C_0, {k,h',w_1} in C_1

are disjoint: the four hub points are distinct, each w_i avoids all
four, and w_0!=w_1. This contradicts core cross-intersection. Thus
w_0=w_1=w, where w is a fresh label distinct from all of R,T,H_0,H_1.
The geometry is now

    H_0={h,h'}, H_1={k,k'},
    U_0={k,k',w}, U_1={h,h',w},                    (3)

with the five displayed exterior core points h,h',k,k',w distinct.
No identification of w with the triangle point c has been made.

## A second actual anchor has neighbourhood at most40

The four common core tails {h_i,k_j,w}, for h_i in H_0 and k_j in H_1,
occur in both D_0,D_1. In particular Q={0,h,k,w} is an actual member.
Its four points are distinct. Their total degree is at most

    d(0)+d(h)+d(k)+d(w)<=13+15+15+15=58.

The complete0-link consists of K_0 and D_0, and K_0 avoids the five-point
core of D_0. The Q8 degrees inside that core therefore give exactly

    d(0,h)=5, d(0,k)=4, d(0,w)=4.

The following displayed actual members give the other three pair lower
bounds. Each row contains four distinct members; their validity follows
directly from the core families in (3).

| Pair | Four actual members containing it |
|---|---|
| hk | 0hkw, 1hkw, 0hkk', 1khh' |
| hw | 0hkw, 1hkw, 0hk'w, 1hk'w |
| kw | 0hkw, 1hkw, 0h'kw, 1h'kw |

For the first row, the two members with root0 differ by w versus k';
the two with root1 differ by w versus h'. The other rows are distinct
because the root labels differ or the second hub partner differs. All
core points avoid the roots, so none of these distinctions collapse.
Thus each of d(h,k),d(h,w),d(k,w) is at least4, and the sum of Q's
six pair codegrees is at least5+4+4+4+4+4=25.

Every global triple codegree is at most2: three distinct extensions
of one triple would themselves be a sunflower. Hence the sum of the
four triple codegrees inside Q is at most8. Exact inclusion-exclusion,
using simplicity and the fact that Q itself is actual, now yields

    N(Q)=sum_(v in Q) d(v)-sum_(e in binom(Q,2)) d(e)
            +sum_(A in binom(Q,3)) d(A)-1
        <=58-25+8-1=40.

This contradicts N(Q)>=41. It excludes the last geometry and completes
the stated all-singleton8, zero-triple N43 subcase.

## Dependency and scope record

The proof's substantive local imports are B4, I8/isolation, H27 and HP15.
The ordinary triangle lemmas used above are in
`LOW15-large-singleton-core.md`, SHA256
`164460b2b3c60fe6bcf6ea36164350ef949efc253d74e3236f08fd6d6225d482`.
Their source boundary is `PRIOR_DELTA18_UNLOCK.md`, SHA256
`25b65f695264ae0dbcd5d97b8e66eac421cccbb9970eaf20cc8692886f855b89`.

The earlier `LOW15-N44-N43-core-route.md`, SHA256
`25fdfcf37e85b76a1e656ab241860456b8286a640487a06c0ee99dcd291c50e1`,
left precisely the low-root Q8-leaf issue open in this subcase. The
current proof resolves it without altering that frozen note. Profiles
with singleton counts below8 or with positive exact triple counts are
outside the theorem stated here.
