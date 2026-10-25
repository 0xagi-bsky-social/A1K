# Ordinary closure of the ten one-low N45 profiles

23 October 2026. Substantive proof development, not a final audit or a
global67 claim. There is no LP, exterior-support cutoff, or geometric
enumeration in this note. All exterior labels and identifications remain
arbitrary. The finite arithmetic signature list is the small exact census
`LOW15-high-profile-census.json`, source SHA256
`bf5fe9e36909c5ad4f732b2490c613d93c9d69e409c48004cf897e6586c10c7d`
and data SHA256
`8d4bebfd94168829f559ad083dfbf15f8e6e18456bc43754e01d477e8ec4d114`.

## Domain and common local facts

Assume a hypothetical simple SF4 family F of68 members, mu>=41, global
point cap15, the newly proved exact singleton cap9, and the stated H27,
B4, classification/isolation and crowding/cross-star imports. Consider
an actual anchor R={0,1,2,3} with N=45, T=0, and sorted singleton counts
(7,8,9,9). The preceding arithmetic/B4/triangle deductions leave exactly
the ten canonical rows below. Pair order is01,02,03,12,13,23.

Write E_ij for the exterior two-sets of the exact pair category ij.
Their sizes are p_ij. A category of size2 is a two-edge path; a category
of size3 is a triangle. A root i is called good here if s_i>=8 and its
pair-row r_i is at least5. The ordinary local triangle lemma gives:

* all E_ij at a good i lie on a triangle A_i;
* every edge has multiplicity at most2 there, by triple codegree;
* the entire far singleton family at i avoids R union A_i, including
  both Q8 leaves, by the near two-edge matching argument.

These facts are proved in `LOW15-large-singleton-core.md`; the Q8 leaf
step was independently checked in `NO43-Q8-leaf-check.md`. Two good roots
sharing a category of size at least2 have equal triangles. If a good root
has category sizes(3,1,1), its two singleton exterior edges are distinct:
otherwise the triangle category supplies their third occurrence and
violates triple codegree2. Those two edges can also identify triangles.

For any root with s_i>=8, even if r_i=4, B4 still makes its near family
intersecting. Thus edges from different categories incident to i must
intersect. The row4 roots below have singleton9; the triangle lemma itself
is not applied to their full near family.

## The exact ten rows

The prefix for each ID is CAP15_HIGH_.

| ID | p=(01,02,03,12,13,23) | s=(0,1,2,3) | r=(0,1,2,3) |
|---|---|---|---|
|044|(0,1,3,3,2,2)|(9,9,8,7)|(4,5,6,7)|
|047|(0,1,3,3,3,1)|(9,8,9,7)|(4,6,5,7)|
|065|(0,2,2,2,3,2)|(9,9,8,7)|(4,5,6,7)|
|079|(0,2,3,3,2,1)|(9,9,7,8)|(5,5,6,6)|
|083|(0,2,3,3,3,0)|(9,7,9,8)|(5,6,5,6)|
|106|(1,1,2,2,2,3)|(9,9,8,7)|(4,5,6,7)|
|116|(1,1,2,3,1,3)|(9,9,7,8)|(4,5,7,6)|
|125|(1,1,3,3,1,2)|(9,9,7,8)|(5,5,6,6)|
|133|(1,2,2,2,2,2)|(9,9,7,8)|(5,5,6,6)|
|137|(1,2,2,2,3,1)|(9,7,9,8)|(5,6,5,6)|

These are arithmetic rows, not assumed actual cores. We show directly that
every attempted arbitrary-support core with each row is impossible.

## Five rows with three good roots

For079,083,125,133,137, the three roots with singleton at least8 are good.
Their triangle supports are identified as follows:

| ID | Good roots | Identifying categories |
|---|---|---|
|079|0,1,3|03 and13, both of size at least2|
|083|0,2,3|02 and03, both of size at least2|
|125|0,1,3|03 identifies0,3; distinct singleton edges01 and13 identify1|
|133|0,1,3|03 and13, both of size2|
|137|0,2,3|02 and03, both of size2|

For125, at root1 the categories01 and13 are singletons and12 is a
triangle. The two singleton edges are distinct and each belongs both to
A_1 and to the already common triangle A_0=A_3. Thus all triangles agree.

Call this common triangle A. The remaining root, whose singleton count
is7, has a positive category to a good root. Choose any actual member B
in such a category. Its exterior edge lies in A. Its complementary two
root points are good, and both of their far singleton families avoid
R union A. If any two tails from these families were disjoint, their
actual lifts and B would be three pairwise disjoint members. The two
far families are therefore cross-intersecting. Their centres are outside
both supports, and their sizes sum to at least16. HP15 contradicts this.
No isolation statement at the singleton7 root was used.

## Rows044 and047: a shared edge is enough

The good roots1,2 share the size3 category12, so their triangle supports
agree; call the triangle A. Category02 is a single edge f of A. Category03
is a triangle B. Root0 has singleton9, so B4 requires its edge f to meet
every edge of B. A two-set covering all edges of a triangle is one of
that triangle's edges. Consequently f is an edge of B as well.

The actual member {0,3} union f is thus present and has its support inside
R union A. It avoids roots1,2, whose far singleton tails avoid R union A.
It witnesses cross-intersection of those two actual large pools exactly
as in the preceding argument. Their sizes are9 and8, in either order,
contradicting HP15. It is unnecessary to identify all of A and B.

## A literal extension obstruction at the singleton7 root

The following elementary observation will handle065 and106. Suppose a root
l has two incident categories, with different partners a,b, that are a
full triangle A and a two-edge path on A. Let a third incident category
have partner c distinct from a,b,l. An exterior edge {u,w} of this third
category with u in A and w outside A is impossible.

Indeed, the two-edge path has an edge {u,v} through every u in A. The full
triangle has another edge {u,v'} through u, with v' different from v.
Together with {u,w}, these are three edges with pairwise intersection
exactly {u}. Their lifts with partners a,b,c and common root l are three
actual four-sets whose pairwise intersections are exactly {l,u}, a
sunflower. This uses only actual pair members and does not use B4 at l.

## Rows065 and106: the entire row7 is forced onto a triangle

In both rows, good roots1,2 share category12 of size2. Their triangles
agree, say A. At the singleton7 root3, categories13 and23 are respectively
a triangle and a two-edge path in065, and a two-edge path and a triangle
in106. The remaining category03 has size2.

Every edge of E03 must meet A. In065, B4 at root0 makes it meet both
edges in E02, which are on A. In106, B4 at root0 makes it meet the single
edge in E01, which is on A. The literal obstruction just proved forbids
an edge meeting A in exactly one point. Therefore every E03 edge is
entirely on A. All seven pair members through root3 now use edges of A.
Each of its three edges has multiplicity at most2 by triple codegree,
so at most6 are possible. This contradicts r_3=7.

## Row116: identify two triangles before using the last edge

The good roots are1 and3. Write A=A_1 and B=A_3. Their common category13
is a single edge f. Category12 is the full triangle A; category23 is the
full triangle B; category03 consists of two edges of B.

Suppose A and B have different supports. Since both contain f, write
f={u,v}, A={u,v,a}, B={u,v,b}, where a,b,u,v are distinct. At root3,
the edge f already occurs once in E13 and once in the triangle E23.
Triple codegree forbids its occurrence in E03. Thus E03 consists exactly
of {u,b} and {v,b}.

Category01 is a single edge g of A. B4 at root0 requires g to meet both
{u,b} and {v,b}. Since b is outside A, this forces g={u,v}=f. But at root1,
the same edge f then occurs in E01, E13 and the triangle E12, contradicting
triple codegree2. Therefore A=B.

At the singleton7 root2, categories12 and23 are now two full copies of
the same triangle A with different root partners. Category02 is one edge e.
B4 at root0 forces e to meet both edges in E03, so e meets A. If e lies
inside A, its occurrence in E02 is the third use of that triangle edge
at root2, contradicting triple codegree2. If e={u,w} has only u in A,
choose two different triangle edges through u, one in E12 and one in E23.
Their actual lifts together with the E02 member form a sunflower with
core {2,u}, exactly as in the extension obstruction. Both cases fail.
This excludes116.

## Result and boundary

All ten surviving N45 rows with singleton multiset (7,8,9,9) are excluded
by actual-member arguments on arbitrary exterior support. The only N45
arithmetic rows remaining after the other recorded deductions are the
three two-low rows with singleton multiset (7,7,9,9), handled in the
separate two-low investigation. No claim about those three rows is made
here, and no global maximum-degree15 exclusion follows from this note
alone.

The HP15 uses in the first seven cases require the imported cross-star
theorem in its proved mu>=41, Delta<=18 domain. The other three cases
065,106,116 use literal sunflowers, B4 and triple codegree only. The
finite arithmetic coverage and the ordinary structural proof play
different roles; neither is described as a completed Lean proof.
