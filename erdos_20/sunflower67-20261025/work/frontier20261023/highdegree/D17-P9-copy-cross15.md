# D17 P9: actual copied-block cross-star bounds

23 October 2026. Ordinary proof and discovery-model bridge. No cap16
reduction, support cutoff, solver result or Lean proof is assumed.

Let F be finite simple SF4 with mu>=41 and Delta<=18. Let its actual
x-star contain H=P9=P10 minus B on six points Y, and put C=Y minus B.
For every point z outside {x} union Y, consider the actual subfamilies

    J_B(z)={T in H union {B}: {z} union T belongs to F},
    J_C(z)={T in H union {C}: {z} union T belongs to F}.

Both are intersecting: H is intersecting, and each of B,C meets every
H block. Each is SF3 because all its z-lifts are actual members of F.
Both are cross-intersecting with the nine actual x-tail blocks H. The
distinct centres x,z lie outside Y and hence outside both tail supports.
The previously imported actual-star HP15 theorem therefore gives

    |J_B(z)|<=6,             |J_C(z)|<=6.                  (1)

These are two separate applications. H union {B,C} is not asserted to
be intersecting: B and C are disjoint. No copy at z is assumed to exist
merely because an automorphism could produce it.

## Exact v9 projection

For each represented point z outside x+Y in a literal P9 branch, the
model adds one coefficient-one row on the full four-point trace masks
{z} union T for T in H union {B}, and a second for H union {C}. Both
right sides are6. A full four-point trace is exactly one actual member,
with no unrepresented completion and no multiplicity. Every root cone
contains x, so no prescribed-root offset occurs in either row. Points
outside the represented universe receive no row; their omission only
weakens the necessary relaxation. P10 branches receive no such rows.

The v9 replayer independently reconstructs the canonical nine H blocks,
B and C, every represented exterior centre and each full four-trace
column, then checks all coefficients and RHS values and the absence of
selector columns. It retains HP15 as a pinned prior ordinary/finite
input, rather than claiming to re-prove that theorem.

## Conditional whole-Z singleton bound: ordinary fallback only

The following stronger observation is recorded for future use, but is
not added as a v9 model row. Suppose an actual Q is wholly inside the
opposite root support Z, with Q disjoint from Y and x. Let v be in Z
minus Q and let K_Q be the nonempty set of complete opposite root-link
triples whose cones avoid Q. Suppose v belongs to every U in K_Q.
Every root-avoiding member with exact Z trace {v} avoids Q and hence
belongs to the intersecting family D(Q). It meets every xH cone, so
has at least three Y points. Since it already contains v, it has
exactly three Y points and is v+T for T among H,B,C.

Both B and C cannot occur at v: the actual members v+B,v+C and any
surviving x+U have all pairwise intersections exactly {v}. Therefore
this entire singleton pool equals an actual subfamily of H+B or H+C
at v. Applying (1) bounds the whole Z-singleton pool by6. If a surviving
U does not contain v, the same intersecting-complement argument instead
makes this singleton pool empty.

For the saved P9-Q8 IZ04 marker Q={8,9,10,11}, the surviving cone tail
is U={6,7,12}; thus the exact-Z singleton pool at12 is at most6. This
statement uses the actual marker and complete root link, not a global
intersecting-pool assumption for arbitrary Q8. It is an analytic
fallback; v9 contains only the two unconditional copied-block rows (1).
