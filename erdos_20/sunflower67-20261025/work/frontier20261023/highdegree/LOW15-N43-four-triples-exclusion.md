# N43 cannot have all four exact triple categories

24 October 2026. Ordinary proof development on arbitrary exterior support.
No solver, enumeration, or Lean result is used in this deduction.

Assume the established cap15 domain: |F|=68, mu>=41, no P9/P10 in
point-links, singleton cap8, H27, B4, I8 classification/isolation, HP15.
Let R=0123 be actual with N(R)=43 and all four exact triple categories
nonempty. Write their actual members as Q_i=(R minus i)+z_i, where
z_i is outside R. The degree identity gives S>=28+4=32, hence all
singletons8. Equality forces all four degrees15 and all pair rows3.

At each i, the exact-singleton family D_i has8 members, and the near
link K_i has7 members and is intersecting by B4. For every pair ij,
all its exterior edges must contain z_i and z_j: apply intersection
of K_j to Q_i and an ij member, and reciprocally at i. Consequently
p_ij<=1 if z_i differs from z_j. If they agree, p_ij<=2 by global
triple-codegree2 at {i,j,z_i}.

We will repeatedly use the following elementary strengthening of core
isolation. If a point w has two disjoint edges in its point-link inside
K_i, then every triple of D_i avoids w. This is immediate for P8/P9/P10
isolation. For Q8, K_i avoids the five-point core by B4; if w were one
of its leaves, the far leaf triple supplies an edge between its two
far hubs in the w-link, disjoint from the entire near support. Together
with the two near edges this is a forbidden three-matching. Thus the
claim also handles Q8 leaves, without isolating them indiscriminately.

There are five equality-partition types for the four exterior centres.

## Four distinct centres

Every pair count is at most1, and every row is3, so all six counts are1.
At root i, the point z_i in K_i then has the three disjoint edges
{j,z_j}, j in R minus i. This is a forbidden three-matching.

## All equal, or three equal

If all centres equal a, every root pair ij already occurs in two triple
members containing a. No ij pair member can contain a, contradicting
the positive pair rows. If three centres equal a and the fourth differs,
each pair from the exceptional root to a common-centre root has the
other two common-centre triple members containing that root pair and a.
Its pair members also must contain a, so every such category is empty.
The exceptional root's row would be0, not3.

## Two pairs of equal centres

Relabel so z_0=z_1=a, z_2=z_3=b, with a different from b. Put
w=p01=p23; equality follows from the four row equations. Cross-category
counts are at most1 and w at most2, so w is1 or2. If w=1 all four
cross categories occur. If w=2 they form a perfect matching; relabel
within the two groups so the matching is02,13. In either case the
actual member E=02ab occurs.

Both D_1 and D_3 avoid a,b. To see this at root1, its near triples include

    023, 23a, 03b, 02b.

For w=1 they also include 0ac,2ab,3ab for some c outside R+a.
The a-link has disjoint edges23 and0c, while the b-link has disjoint
edges03 and2a. For w=2 the extra near triples are0ac,0ad,3ab with
c different from d. The a-link again has23 and0c, and the b-link has
02 and3a. The reciprocal statement at root3 follows by exchanging
the two groups and a,b. The preceding matching lemma applies.

The two exact-singleton tail families D_1,D_3 are intersecting and
their restored four-set stars avoid E: their tails avoid R,a,b.
If one tail from each were disjoint, the two restored members and E
would be an empty-core sunflower. The tails are therefore cross-
intersecting. Their actual stars have total size8+8=16, contradicting
the imported HP15 theorem in its mu41/cap15 domain.

## One repeated centre and two distinct centres

Relabel z_0=z_1=a, z_2=b, z_3=c, where a,b,c are distinct. Rows2,3
force every cross category incident with either of them to have count1.
The remaining row equations give p01=1 as well. Its member is01ad.
The actual Q_2=013b and Q_3=012c intersect in01. Unless d is b or c,
they and01ad form a sunflower with core01. Exchange roots2,3 if needed
and take d=b. Thus E=01ab is actual.

At root2 the near triples are

    013, 13a, 03a, 01c, 0ab, 1ab, 3bc.

The a-link has disjoint edges13 and0b; the b-link has disjoint edges
0a and3c. At root3 the near triples are

    012, 12a, 02a, 01b, 0ac, 1ac, 2bc.

The a-link has disjoint edges12 and0c; the b-link has disjoint edges
01 and2c. Thus D_2,D_3 both avoid a,b. The actual E forces these two
size8 tail families to be cross-intersecting exactly as before, again
contradicting HP15.

All equality partitions are exhausted. Therefore an N43 anchor has
at most three exact triple members. This does not by itself exclude
N43 with fewer triple categories or classify rho<=6 links.
