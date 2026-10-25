# Ordinary literal P9 complement profiles

23 October 2026. New ordinary proof development, independent of the cap16
no-P9 conclusion. No solver, model construction, replay or Lean claim.
Earlier complement notes and v7 source hashes remain unchanged.

Let F be finite simple SF4 with mu>=41 and Delta<=18, so the already
imported actual-star HP15 theorem applies. Suppose the complete point-link
at x is H union K, where H is P9 on six points Y and every K triple
avoids Y. This is an explicit complete-link premise. Let Q be an actual
member disjoint from {x} union Y, and define

    K'={U in K: U intersect Q is empty},
    k=|K'|, J_K=intersection_(U in K') U when k>0,
    I=D(Q).

I is intersecting, and its complete x-link is precisely H union K'.
The ordinary bounds below depend only on these literal surviving cones.

If k=0, the complete-P9 capacity argument gives |I|<=20, including
internal Y four-sets. Its proof is in `P9-disjoint-complement22.md` and
frozen `paper/main.tex:1124--1144`. If k>0, every member of I avoiding
x meets all H cones and all K' cones. P9 has no transversal of size at
most2, so that member has exactly three Y points and one exterior point
in J_K. Thus there are no internal four-sets in this case.

The triple transversals of H=P10 minus B are H itself, B and C=Y minus B.
The nine H traces have at most one extra completion each, after their
prescribed x-cone consumes one unit of triple-codegree2. The two
exceptional trace classes have total count at most2: if both occur,
intersection forces all exterior centres to coincide, and simplicity
leaves one in each class; a single class has triple capacity2. Hence

    |I|<=20+k.                                            (1)

In fact B and C cannot both occur when k>0. If z+B and w+C occur,
intersection of I forces z=w. That point belongs to every U in K'.
Then z+B,z+C,x+U have all pairwise intersections exactly {z}, a
forbidden sunflower. This observation uses only the actual three
members, and neither cardinality68 nor global cap16.

If J_K is empty, there are no x-avoiders and

    |I|=9+k.                                              (2)

If J_K={z}, the x-avoider tails at z consist of a subfamily of H and
at most one exceptional trace. They form an actual intersecting SF3
family, since either exceptional is a transversal of every H block.
They are cross-intersecting with H at x, with both centres outside Y.
HP15 bounds their size by6. Therefore

    |I|<=15+k.                                            (3)

For k>=3, J_K has size at most1: three actual root cones containing
x and two common points would violate triple-codegree2. When J_K is
a singleton, k<=6 by pair-codegree6 on x,z. Consequently (1)--(3),
together with k=0, recover the uniform bound22 from the earlier note
and supply sharper bounds whenever the actual surviving cones permit.
In particular k1 gives21; k2 with two common points gives22, with one
common point gives17, and with empty intersection gives11. For k>=3,
use9+k if the intersection is empty, and15+k otherwise. Global root
size at most18 bounds the empty-intersection case by18.

## D17 projection and exact offsets

The D17 model has complete root degree17 and a literal P9-plus-I8 link.
For each fixed actual Q outside x+Y it computes all K' from those exact
root cones, including every surviving cone. It takes the minimum of
applicable bounds above and the prior uniform cap22. Denote it c_Q.
With residual trace variables c_s, its rows are

    sum_(s intersect Q empty) c_s <= c_Q - r_Q,
    -sum_(s intersect Q nonempty) c_s <= a_Q - (68-c_Q),

where r_Q and a_Q count root cones respectively disjoint from and meeting
Q. The second follows from |F|>=68. These are separate necessary rows
because the relaxation does not impose a fixed residual total. Selected
actual residuals are still variables, so only root cones are offsets.
All Q points are represented; thus trace intersection with Q is exact
for arbitrary exterior completions. No support cutoff is assumed.

A pure Z-internal Q leaves at most three points in a Q8 support, or two
in a P8 support. It therefore has k<=1 in the former and k0 in the latter.
This yields cap20/21 and neighbourhood48/47 directly, without any
Y-internal absence premise or use of cap16 no-P9.

The v8 implementation preserves v7 as a separate file and pins this note.
The full model still imports B4, classifications, H27 and the prior HP15
certificate provenance. The new row arithmetic does not independently
prove those premises. The exact literal-transversal tables, actual-Q
guards, surviving-cone intersections and every row coefficient/offset
are reconstructed by the dedicated v8 replayer before weighted arithmetic.
