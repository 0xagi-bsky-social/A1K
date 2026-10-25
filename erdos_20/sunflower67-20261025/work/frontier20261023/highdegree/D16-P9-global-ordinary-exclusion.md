# Ordinary global no-P9 consequence at cap16

23 October 2026. New ordinary proof development, not a final audit or Lean
claim. No solver, enumeration, model construction or certificate replay
was run. This note adds a literal sunflower observation to the frozen
complement22 argument, then treats roots of degree at most15 by counting.

**Conclusion.** Under the named prior/imported results, a simple SF4
family of68 members and global maximum degree16 has no P9 subfamily
in any point-link. Consequently every exact singleton count is at most8.
The degree16 eight-plus-eight alternative is not excluded by this note.

## Dependency order

We use H27, universal pair/triple codegrees6/2, P9 isolation, the
complete-C5 lemma, the guarded actual cross-star theorem HP15, and:

* `D16-P10-ordinary-exclusion.md`: no P10 point-link;
* `D16-NO47-ordinary.md`: every actual neighbourhood is at most46;
* `P9-disjoint-complement22.md`: every actual outside Q has at most22
  disjoint members, retaining the complete outside link K';
* `D16-P9-root16-ordinary-exclusion.md`: no degree16 root has a P9
  component.

The fourth result is needed only at the end, to combine with the present
argument for root degree at most15. Its proof does not use the present
global conclusion, so the dependency order is acyclic. The older
complement22 note is preserved unchanged; its possible common-point
equality branch is eliminated by the additional witness below.

## Complementary exceptional traces cannot both occur

Consider an intersecting disjoint complement I=D(Q) whose complete
x-link is H union K', where H=P9=P10 minus B on W, and K' is nonempty
and avoids W. Put C=W minus B. Every member of I avoiding x has exact
W trace of size3 and an exterior centre belonging to every triple of K'.

If both exceptional traces occur, say {z} union B and {w} union C,
intersection of I forces z=w: B and C are complementary within W,
and z,w are outside W. For any U in K', z belongs to U. The three
actual members

    {z} union B,       {z} union C,       {x} union U

then have all three pairwise intersections exactly {z}. They are
distinct because the first two avoid x and have different W traces.
This is a forbidden sunflower. Therefore at most one of B,C can occur
in I when K' is nonempty.                              (1)

For k=|K'|>=3, the common intersection of K' is empty or a singleton,
by triple-codegree2. If empty, there are no x-avoiders. If it is {z},
each exceptional trace has at most one completion, because its centre
is fixed. By (1), at most one exceptional trace occurs. The H-block
copies together with that exceptional trace, when present, form an
actual intersecting SF3 tail family at z which is cross-intersecting
with H at x. Both centres are outside W, so HP15 bounds the total
number of x-avoiders by6. Hence

    |I|<=9+k+6=15+k<=21,                                  (2)

where k<=6 follows from the global pair-codegree of x,z. The same
estimate on avoiders holds for k=2 if its two triples have exactly
one common point. The common-intersection-empty case has
|I|<=d(x)<=16.

Consequently, whenever NO47 gives |D(Q)|>=22, equality in the
complement22 bound has only one possible form:

    k=2, |D(Q)|=22, and eleven x-avoiders of exact W trace3. (3)

The k=0 case has bound20, and k=1 has bound21 by the older elementary
capacity count. This conclusion does not need K to have seven or
eight triples and does not use any I7 or I8 classification.

## Every remaining P9 root has many triple traces

Suppose a point x with m=d(x)<=15 has a P9 component H on W. No-P10
and isolation give the complete link H union K with K wholly outside
W. Count the n=68-m members avoiding x by exact W trace sizes, using
O,H_1,P,E,I_4 for sizes0,1,2,3,4 and total incidence D.

The combined trace0/trace1 family is intersecting, since P9 avoids
every set of at most two support points. H27 gives O+H_1<=27.
Initially D<=6*16-27=69. The exact identity

    2n=D+H_1+2O-E-2I_4

therefore implies O>=2n-96>=10. Choose an actual outside Q.
Since |D(Q)|>=22, its surviving K' cannot be empty. Any actual
four-subset of W would be disjoint from Q and a surviving K'-cone,
giving an empty-core sunflower. Thus I_4=0 globally.

The three C5 points of P9 now have degree at most15, by completeness
of their prescribed pair-links and the complete-C5 lemma. The other
three points have degree at most16. This improves the incidence cap to

    D<=3*15+3*16-27=66.                                   (4)

Equation (3) supplies eleven actual x-avoiders with exact W trace3
in D(Q), hence

    E>=11.                                                (5)

Since n=O+H_1+P+E and O+H_1<=27,

    P+E>=41-m.                                            (6)

## The nine-cone average forces impossible equality

Let W_sum be the sum over the nine prescribed x-cones A of the number
of x-avoiders meeting A. Every actual cone has neighbourhood at least41,
so

    W_sum>=9*(41-m)=369-9m.                               (7)

A singleton W trace meets at most5 P9 blocks, a pair at most8, and a
triple at most9. More precisely, the singleton weight is5 exactly at
the three C5 points C=W minus B, and a pair's weight is8 exactly when
both its points lie in C; all other singleton/pair weights are4/7.
With I_4=0,

    W_sum<=5H_1+8P+9E
         =5D-2P-6E
         =5D-2(P+E)-4E
         <=330-2*(41-m)-4E
         =248+2m-4E.                                     (8)

Combining (7),(8),

    121<=11m-4E<=11*15-4*11=121.

Every inequality is therefore an equality. In particular

    m=15, E=11, D=66, P+E=26, hence P=15 and H_1=3.

Equality in the meeting-weight bound in (8) requires every actual pair
trace to lie entirely in the three-point C5 set C. But at each C5
point the universal full pair-pool count is at most6. The proof is
the star/triangle argument expanded in `D17-P10-ordinary-closure.md`:
exterior edges from pair traces intersect, a star consumes global
pair capacity6, and a triangle has three edges each of multiplicity
at most2. It applies equally to each C5 point of P9.

All P=15 pair traces are within C, so summing the three pair-pool
bounds counts each twice and yields

    30=2P<=3*6=18,

a contradiction. Thus no root of degree at most15 can contain P9.

Combining this with the already established exact degree16-root
exclusion proves global no-P9 at cap16. Since an exact singleton
family is intersecting SF3 and every nine-member such family is P9,
all exact singletons are consequently at most8.

## Scope and source boundary

The proof includes arbitrary exterior completions and all nonblock
triple traces. Equality in the upper count is used only after a chain
of inequalities whose ends agree. The pair-pool cap is applied solely
at the three C5 vertices, not to an unrestricted P5 pair pool.

The frozen prior repository is
`work/frontier20261020/prior-art68/repository`, pinned commit
`90c03c79bcf44eb8f61dff1b86091b822cc4cd3c`.
The ordinary pair-pool source is
`companion/upstream/D18_P10/PROOF.md:62--97`. P9 block incidences and
isolation are at `paper/main.tex:206--231,272--331`; the guarded
cross-star theorem and its finite-certificate dependency are at
`1001--1024`. The other dependencies are the explicit notes listed
above, including the complete-C5 classification boundary.

This is not a proof that every degree16 link is excluded or that the
global extremal bound is67. No new solver or Lean assurance is claimed.
