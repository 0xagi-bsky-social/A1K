# Size15 SF3, rho at most6: partial ordinary reduction

24 October 2026. This records earlier partial research so its scope is
durable. It is not a classification, extension theorem, or Lean result.
No computation was performed while writing this note.

Let L be a simple SF3 family of size15 with rho(L) at most6. Every actual
triple has closed neighbourhood at least9. Universal point degrees are
at most6 and pair codegrees at most2.

## Minimum degree and derived support bounds

A degree-one point x in xyz cannot have a degree-six neighbour: a
degree-six point-link consists of two triangles and all used pairs
therefore have codegree2. Thus d(y),d(z) at most5. Inclusion-exclusion
gives N(xyz)=d(y)+d(z)-d(yz), so N at least9 forces both degrees5 and
d(yz)=1. But a five-edge SF2 graph is C5 or triangle plus a two-edge
path. In the y-link the edge xz has x of degree1; it must lie in the
path, with z its middle point of degree2. Contradiction. Every used
point consequently has degree at least2.

Let I be the number of unordered intersecting pairs of triples. Then
I at least15*8/2=60. Write r(v) for the number of neighbours w with
d(vw)=2. Exact double counting gives

    I = sum_v [binom(d(v),2) - r(v)/2].

For degrees2,3,4,5,6, an SF2 point-link has r(v) at least0,1,2,4,6,
respectively. Thus its summand is at most1,5/2,5,8,12. On this finite
degree range it is at most(11*d-18)/4. Since sum d=45, the number n
of used points satisfies 60<=495/4-9*n/2, hence n<=14.

If maximum degree is at most5, the summand is at most(7*d-11)/3,
giving n<=12. If maximum degree were at most4, the summand is at most
2*d-3, giving n<=10; but sum d=45 would require n>=12. Thus a degree5
or degree6 point exists. These are proved support bounds, not assumed
ambient cutoffs.

## Degree-two motifs, still incomplete

If a degree-two point x has a degree-six neighbour a, the a-link forces
the two triples xab,xac and the third abc. Inclusion-exclusion gives
N(xab)=4+d(b), so b has degree5, and similarly c has degree5. The b-link
has the path x-a-c and a disjoint triangle D; the c-link has x-a-b and
a disjoint triangle E. The other triangle in the a-link is T. Thus L
contains the twelve triples

    xab, xac, abc,
    a*binom(T,2), b*binom(D,2), c*binom(E,2),

where all three triads avoid x,a,b,c. The points x,a,b,c are saturated.
There remain three triples avoiding those four points. An earlier tiny
literal diagnostic normalized identifications among T,D,E and reported
no permissible thirteenth triple, but its complete source/witness output
was not saved. That observation is NOT used here as a proved exclusion.
It would require a fresh bounded certificate or an ordinary argument.

If x has degree2 and no degree-six neighbour, its triple xyz forces
d(y)=d(z)=5, d(xy)=d(xz)=1 and d(yz)=2. The five-edge point-links then
have path components x-z-w and x-y-w, with the same w supplied by the
second yz triple. Consequently the known triples are xyz,yzw,
y*binom(D,2),z*binom(E,2), and the second triple through x. The triads
D,E avoid x,y,z,w. The remaining six triples disjoint from xyz form an
intersecting family. This branch is unresolved in the present notes.

The exact-rho7 theorem in `LOW15-R15-rho7-classification.md` is separate.
None of these incomplete degree-two arguments is needed for NO44.
