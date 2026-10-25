# A guarded P9 disjoint-complement bound of22

23 October 2026. Ordinary proof development, not a final review or formal
verification. No solver, enumeration or Lean process was run. This note
checks and strengthens the complete-link argument developed in
`LOW15-two-low-core.md` without changing that frozen note.

## Exact hypotheses

Let F be a finite simple SF4 family with mu>=41 and Delta<=18, so the
imported actual cross-star theorem HP15 applies. Let x be a point whose
complete link is

    L_x = H union K,

where H=P9=P10 minus B on six points W, and every member of K avoids W.
The union is disjoint. This exact isolation premise is essential: a
possible missing P10 block must first be excluded, for example by a
separate no-P10 theorem. No classification or support bound on K is
assumed.

For every actual Q disjoint from {x} union W, put I=D(Q). Then

    |I|<=22.                                               (1)

The imported inputs beyond HP15 are the universal pair/triple codegree
bounds6/2, the P9 transversal description, and the bound20 for an
intersecting SF4 family with a complete P9 point-link. The latter includes
internal four-sets; see frozen `paper/main.tex:1124--1144`.

## Retain the whole surviving link

I is intersecting: two disjoint members of I, with Q, would be an
empty-core sunflower. Its complete x-link is H union K', where

    K'={U in K : ({x} union U) is disjoint from Q},
    k=|K'|.

If k=0, the complete-link bound gives |I|<=20. Suppose k>0.
Every member of I avoiding x must meet all nine H cones, so it uses
at least three W points. It also meets every K' cone, whose tail is
outside W. It must therefore have exactly three W points and one
exterior point z, with z belonging to every member of K'.

The three-point transversals of H are its nine blocks together with
B and C=W minus B. Each H-block trace occurs in at most one x-avoiding
member, because its prescribed x-cone consumes one unit of global
triple-codegree2. The two exceptional trace classes B,C have combined
size at most2: if both occur, intersection of I forces every exterior
point on one side to equal every exterior point on the other, leaving
one member in each class; if only one occurs its triple codegree is2.
Consequently

    |I|<=9+k+9+2=20+k.                                    (2)

This proves (1) when k=1 or2.

## The strengthened common-point estimate

For k>=3, the common intersection of K' has size at most1. Otherwise
three actual x-cones would contain the same triple {x,a,b}, violating
triple-codegree2. If the intersection is empty, I has no members avoiding
x and |I|=9+k<=d(x)<=18.

Otherwise its common intersection is {z}. Every x-avoiding member of I
has the form {z} union T for a transversal T on W. Let J be the subset
of H occurring this way, and let e be the number of exceptional traces
B,C occurring. Since z is fixed and F is simple, e is0,1 or2.

If e=0, the actual z-tail family J is an intersecting subfamily of P9
and is cross-intersecting with the actual x-tail family H. Both centres
x,z are outside W. HP15 therefore gives |J|<=6.

If e>=1, choose one actual exceptional trace T0. The family
J union {T0} is also intersecting: T0 is a transversal of H. It is SF3
because all of its z-lifts are actual members of F, and it is
cross-intersecting with H. Its two centres x,z are again outside both
tail supports. Thus HP15 gives

    9+|J|+1<=15,              |J|<=5.

When both B,C occur, apply this reasoning to either one separately.
Their union is not claimed to be intersecting, since B and C are
disjoint. Therefore the number of x-avoiders in I is always at most7:
it is at most6 for e=0 or1, and at most7 for e=2. Hence

    |I|<=9+k+7=16+k.                                      (3)

All k surviving cones contain x,z, so global pair-codegree gives k<=6.
Equation (3) proves (1). In particular no maximum-point-degree bound on
an opposite I7 or I8 is needed for the uniform bound22.

## Equality when d(x)=16

If |I|=22, the proof leaves only the following cases:

* k=2, with all nine H-block completions and exactly two exceptional
  completions present in I;
* k=6, with a common point z and seven x-avoiders, necessarily five
  H-block completions and both B,C at z.

The second case is impossible if d(x)=16. Here |K|=7. The family K is
intersecting: two disjoint K triples together with any H triple would
be an empty-core sunflower in L_x. Six K triples through z have, after
removing z, a six-edge SF2 graph, necessarily two disjoint triangles.
The seventh triple of K avoids z, because the global pair codegree of
x,z is at most6. To meet all six z-triples it would have to cover both
triangles with three points, impossible. Thus an intersecting seven-
triple K has no point of degree6.

Accordingly, at d(x)=16, equality22 requires k=2 and exactly eleven
x-avoiders in I. The two K' triples must intersect in two points:
empty intersection gives no avoiders, while a singleton intersection
gives the same guarded HP15 estimate of at most7 avoiders, valid even
for k=2 when its common point is unique. A three-point intersection
would make the two K' triples identical.

This equality conclusion is a necessary structural condition, not a
complete classification of equality families or an exclusion of them.

## Scope of the resulting neighbourhood reduction

If a size68 family in the above scope has N(Q)<=45 at every actual
member, then |D(Q)|>=23, so no actual Q can avoid {x} union W. If the
global cap is16, this absence is impossible by a whole-support count:
there are n=68-d(x)>=52 members avoiding x, all meeting W; their
exact-one-W subfamily has size at most27 by H27 and the fact that P9
avoids every support pair. Their total W-incidence is at most
6*16-27=69. Hence

    104<=2n<=69+27=96,

a contradiction. Thus NO46 (the bound N<=45), together with no-P10,
would exclude every P9 point-link at cap16. The weaker bound N<=46
leaves the equality cases described above, and must not be treated as
a strict contradiction with (1).

For a degree17 root, an opposite I8 has point degrees at most5, which
also removes the k=6 equality case; nevertheless k=2 can still attain
the upper bound22 in these necessary inequalities. This note does not
close the remaining degree17 branches.

## Source boundary

The prior repository is
`work/frontier20261020/prior-art68/repository`, pinned commit
`90c03c79bcf44eb8f61dff1b86091b822cc4cd3c`.
`paper/main.tex:188--231` supplies the SF2 capacities and P9/P10 models;
`272--331` supplies isolation; `333--350` supplies universal codegrees;
`1001--1024` gives the guarded actual cross-star theorem, with its
explicit finite-certificate dependency; `1124--1144` gives the
intersecting complete-P9 bound20. `LOW15-two-low-core.md` develops the
weaker17+k estimate whose exceptional-transversal step is sharpened here.

No old mu42 bootstrap, support cutoff, minimum-degree assumption,
unproved I7 catalogue, or generic complete-link shortcut is used.
