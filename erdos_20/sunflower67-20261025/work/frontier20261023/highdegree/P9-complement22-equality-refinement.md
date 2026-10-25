# Eliminating the complement exceptional trace in k2 equality

23 October 2026. Additional ordinary research lemma, not needed for the
completed degree16-root P9 proof. No solver or support enumeration is used.
A small 36-pair canonical check suggested the three literal witnesses
below; the displayed sets themselves suffice to verify the argument.

Assume the complete isolated P9-plus-K guard and HP15 scope of
`P9-disjoint-complement22.md`. Suppose an actual disjoint complement I
has size22, exactly two surviving K cones, and eleven x-avoiders. Then
all nine P9 blocks have their unique additional actual copy, and there
are exactly two exceptional copies. Suppose the two surviving K triples
have intersection {a,b}; every x-avoider has its exterior point in {a,b}.

Relabel the canonical P9 so its missing block is B=012 and put C=345.
Its surviving blocks are

    015,023,034,045,124,134,135,235,245.

The following pairs, together with C, are triple sunflowers:

    (034,134,C),  (045,245,C),  (135,235,C),

with pairwise intersections respectively34,45,35. Consequently if the
actual member a+C occurs, no copy b+U can use any of the six blocks
appearing in these pairs: the partner block T has the prescribed x-cone,
and x+T,b+U,a+C would form the same sunflower, as x,a,b are distinct
and outside W. Hence at most the three blocks015,023,124 can be copied
at b. At a, the actual tail family consisting of the copied H blocks
and C is intersecting, SF3, and cross-intersecting with H at x. HP15
bounds its size by6, so there are at most five H copies at a.
There would then be at most eight H copies altogether, contrary to nine.
The same argument applies to C copied at b, regardless of whether its
other exceptional copy is B or C. Thus C has no copy in I.

The two exceptional copies must therefore be a+B and b+B: triple
capacity allows two, their exterior points lie in {a,b}, and simplicity
forces these two distinct choices. At each centre, B together with its
H copies is an intersecting actual tail family cross-intersecting with
H. HP15 bounds that centre's H copies by5. Since there are nine in total,
the H copies split4+5 between a,b.

This proves a necessary equality structure. It does not exclude that
structure by itself, assume a classification of all intersecting SF4
families, or bound the exterior support of F.
