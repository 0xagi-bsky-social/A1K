# P9 complement rigidity and ordinary NO45 at cap15

23 October 2026. New ordinary research argument, not a final review.
The exterior support of the family is unrestricted. This note preserves
all earlier files and repairs, rather than assumes, the complete-link
condition that blocked the earlier generic complement shortcut.

## Imported and previously proved premises

F is a finite simple SF4 family of size68 with Delta<=15. Empty-core
sunflowers are forbidden. H27 gives mu>=41. We use the I9/P9 isolation
lemma, B4, global triple codegree2, and the cross-star bound HP15 in its
already established mu>=41,Delta<=18 scope. The latter bounds two actual
intersecting cross-intersecting SF3 tail families by total size15 when
their distinct centres are outside both tail supports.

`LOW15-mu41-research.md` excludes P10 in any point-link at cap15.
`LOW15-large-singleton-core.md` proves N(R)<=45 for every actual member
R, by first excluding N46 using the common-triangle obstruction.
These two conclusions precede the argument below. Crowding26 still
gives S<=34 at every actual anchor, and exact singleton counts are now
at most9. The complete P9 point-link bound20, including internal
four-sets, is proved in that same new note and in the frozen prior
paper at `paper/main.tex`, lines1124--1144.

## P9 plus a small residual link: exact complement bounds

Let x be a point whose complete link is a disjoint-support union

    L_x = H union K,   H=P9 on a six-point set W,   |K|<=6.

This is the decomposition supplied by P9 isolation. A possible missing
P10 block is absent, because P10 has already been excluded globally.
Thus every triple of K avoids W.

Suppose Q is an actual member outside {x} union W, and let I be all
members of F disjoint from Q. I is intersecting: two disjoint members
of I together with Q would be an empty-core sunflower. Its complete
x-link is exactly H union K', where K' consists of the triples of K
whose cones avoid Q. Write k=|K'|. The neighbourhood bound gives

    |I|=68-N(Q)>=23.

If k=0, the complete-P9 bound gives |I|<=20, a contradiction. Suppose
k>0. Every member of I avoiding x meets every H cone, hence covers H
and uses at least three points of W. It also meets each cone x union U
with U in K', and all such U avoid W. Consequently it has exactly
three W points and one exterior point, and that exterior point belongs
to the intersection of all triples of K'. There are no internal
four-sets in this case.

The triple transversals of H=P10 minus B are its nine blocks, together
with B and W minus B. Each of the nine H blocks can occur in at most
one x-avoiding member, after subtracting its prescribed x-cone from
global triple codegree2. The two complementary exceptional traces
have combined count at most2. If both occur, intersection of I forces
their exterior points to coincide, and each class has size at most1;
if just one occurs, triple codegree2 bounds it by2. Hence

    |I| <= 9+k+9+2 =20+k.

In particular k=1 or2 is impossible because |I|>=23.

For k>=3, the intersection of K' contains at most one point. Three
distinct link triples sharing two points would violate global triple
codegree2 in F after restoring x. If their intersection is empty,
there are no x-avoiders and |I|=9+k<=15, again impossible. Otherwise
write their common point as z. Every x-avoider is now exactly
{z} union T, where T is one of the eleven displayed triple transversals.

Let J count those T that are blocks of H. Their actual z-star tails
form a subfamily of P9. They are intersecting and cross-intersecting
with the nine actual x-star tails H. The distinct centres x,z lie
outside W, so are outside both tail supports. All guards of HP15 hold,
and therefore |J|<=6. The exceptional traces contribute at most2.
We obtain the sharper bound

    |I| <= 9+k+6+2 =17+k.

Since every triple of K' contains z, k<=d_K(z). Thus if the maximum
point-degree in K is at most5, then |I|<=22, again contrary to23.

This is an actual-star application of HP15 to the H-block portion of
the z-tail family. It does not assert that all eleven transversal
types form an intersecting triple family; the two exceptional types
were separated explicitly.

## P9 rigidity under N<=45

**Lemma.** Under the premises above, a P9 component in a complete
point-link has exactly six remaining link triples, all through one
common point.

Otherwise |K|<=6 and its maximum point-degree is at most5. The previous
argument shows that no actual Q avoids {x} union W. Therefore every
member avoiding x meets W. Put n=68-d(x)>=53, and let H_W be the number
of these members having exactly one W point. This exact-one-W subfamily is
intersecting: if two of its members were disjoint, a prescribed x-cone whose P9 block
avoids their at most two W points would be disjoint from both. Such
a block exists because every pair of W points is avoided by a P9
block. This would be an empty-core sunflower. H27 therefore gives
H_W<=27.

The total incidence in W of members avoiding x is at most

    D_W <= 6*15 - 3*9 =63.

We subtract exactly the nine prescribed x-cones; K avoids W. Every
one of the n members meets W, and all except the H_W singletons use
at least two W points. Hence

    106 <= 2n <= D_W+H_W <=63+27=90,

a contradiction. Thus the only possible K has size6 and a point in
all six triples. In particular d(x)=15.

The existence of a P9 component alone has not been excluded: the
six-triple common-point alternative is a genuine remaining case of
this lemma. This is the precise replacement for the invalid generic
complete-link shortcut.

## Application to the three two-small-singleton N45 patterns

For the patterns with sorted singletons (7,7,9,9), N45 forces T=0,
all root degrees15, and each singleton9 root has pair row5. B4 makes
its near family intersecting. The local triangle argument in
`LOW15-large-singleton-core.md` puts its five pair tails on one triangle
with edge multiplicities (2,2,1). Its complete near link consists of
the other-three-root anchor triple and those five pair tails.

A root partner occurs in at most 1+3=4 of these six near triples. An
exterior triangle point occurs in at most4, and there are no other
points. Thus this near K has maximum point-degree at most4, contrary
to the P9 rigidity lemma. This excludes all three two-small-singleton
arithmetic rows without enumerating their exterior completions.

The bounded auxiliary census `LOW15_two_low_core.py` and
`LOW15-two-low-core-census.json` was a discovery diagnostic. It completed
in about0.02 seconds and left168 necessary core assignments after its
weaker guards. It is not an exclusion certificate and is not needed
for this proof.

## Direct exclusion of every N45 anchor

In fact the same rigidity lemma removes the need to enumerate the
remaining N45 profiles at all. Suppose an actual anchor R has N=45.
Use the notation of `LOW15-large-singleton-core.md`:

    D_R=92-S+T<=60,  S<=34,  s_i<=9.

Thus S>=32+T and T<=2. If no singleton count is9, all four must be8,
T=0, and all four root degrees are15. Every pair row is6, and the
common-triangle/HP15 theorem already excludes this case.

Otherwise choose x in R with s_x=9. Its far family is P9, and its near
family K consists of all remaining members of L_x. By isolation they
have disjoint supports. The rigidity lemma says that K has size6 and
all its triples contain a point z. Since R minus x belongs to K,
z is one of the other three root points.

Every near member through x must therefore contain z. A near member
with an exact pair root trace can only have trace {x,z}; its count is
at most3. Exact triple root traces containing x,z have at most two
possible types, each of count at most1. Including R itself gives at
most 1+3+2=6 near triples. Equality |K|=6 forces all these bounds to
be equalities: p_xz=3 and both exact triple types containing x,z occur.
Hence T>=2. The preceding arithmetic now forces

    T=2, S=34, D_R=60, all root degrees15,
    sorted singleton counts (8,8,9,9).

The two actual exact triple members containing x,z omit respectively
the other two root points. Since x already has singleton count9, at
least one of those two omitted roots, say l, has singleton count8.
Its omitted-triple count is t_l=1. Its pair row is therefore

    r_l =15-1-8-2+1 =5.

But the literal triple member Q_l=(R minus l) union {u}, together
with singleton counts at least8 at all three other roots, gives
r_l<=4 by the triple-star bipartite argument proved in
`LOW15-large-singleton-core.md`: B4 forces every incident pair residue
to contain u; removing l,u yields a simple bipartite graph of maximum
degree2 and matching number at most2, hence at most4 edges.

This contradiction excludes N45. Together with the previously proved
N<=45, it yields

    Every actual member has N<=44 when |F|=68 and Delta<=15.

This is an ordinary conditional composition of the named classification,
isolation, H27, crowding and cross-star imports. It neither excludes the
entire Delta15 branch nor asserts the global size bound67 or a Lean
formalization. No new solver certificate or support cutoff is used.
