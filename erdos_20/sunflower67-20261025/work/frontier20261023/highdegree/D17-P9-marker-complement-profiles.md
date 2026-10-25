# D17 P9: sharper complements from literal surviving K cones

23 October 2026. Ordinary research observation and read-only decoding of
saved stage1 receipts. No model import, solver or replay was run. The v7
source and its hash-pinned notes remain unchanged.

Use the complete disjoint-support root link P9(Y) union K from
`P9-disjoint-complement22.md`. For any fixed actual Q outside x+Y, all
surviving K cones are determined exactly by the finite actual root link:

    K_Q={U in K : U intersect Q is empty},       k=|K_Q|.

The root is already absent from Q. The old ordinary proof itself gives

    k=0  => |D(Q)|<=20;
    k=1  => |D(Q)|<=21;
    k=2  => |D(Q)|<=22.

The k=0 bound includes internal Y four-sets, using a genuinely complete
P9 point-link. Thus it does not require Y-internal emptiness.

For a pure Z-internal actual Q of size4, these bounds simplify further.
If K is P8 on six points, only two Z points remain and k=0. If K is
Q8 on seven points, only three Z points remain and k<=1. Therefore all
P9-P8 internal markers have complement cap20 and neighbourhood at least48
at cardinality68. Every P9-Q8 internal marker has cap20 or21, hence
neighbourhood at least48 or47 respectively.

Directly decoding the four saved Q8 stage1 receipt geometries yields:

| Case | Actual Q | Surviving K triple | Complement upper | Neighbourhood lower |
|---|---|---|---:|---:|
| IZ00 | 6,7,8,9 | none | 20 | 48 |
| IZ02 | 6,7,8,11 | none | 20 | 48 |
| IZ04 | 8,9,10,11 | 6,7,12 | 21 | 47 |
| IZ06 | 6,8,11,12 | 7,9,10 | 21 | 47 |

These labels were read from
`degree17_full/P9-Q8-IZxx-internal-Z-stage1-v4-*.json`; the literal
sets and complete-link argument, not those numerical solutions, justify
the table. No relabeling or hidden exterior completion is used.

There is a further optional literal-intersection refinement. For k>0,
every x-avoider in D(Q) has one exterior point in the intersection of K_Q.
If that intersection is empty, D(Q) consists only of its 9+k root cones.
If it is a singleton, the newly proved exclusion of simultaneous B and
Y-minus-B exceptions gives at most6 x-avoiders by HP15, hence upper15+k.
The latter improvement is written in
`D16-P9-global-ordinary-exclusion.md`; its local proof uses only the
mu41/cap18 cross-star scope and the complete P9-plus-K guard, not global
cap16. A future model version should record that added ordinary dependency
explicitly rather than silently changing a note already pinned by v7.

For any such cap c_Q, the exact projected rows are

    sum_(s disjoint Q) count(s) <= c_Q - #disjoint root cones,
    -sum_(s meeting Q) count(s) <= #meeting root cones - (68-c_Q).

Only fixed actual Q qualifies; selected residuals remain in the trace
variables and must not be subtracted twice. The root-cone offset is exact
because every point of Q is represented. Unrepresented exterior support
remains arbitrary. These are stronger necessary conditions, not claims
that any numerical branch has already closed.
