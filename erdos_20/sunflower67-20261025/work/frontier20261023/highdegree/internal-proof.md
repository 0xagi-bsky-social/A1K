# Degree-twenty internal-member exclusion on arbitrary ground sets

Working proof note, 23 October 2026. This is ordinary mathematics with explicitly
imported structural premises and an exact finite coefficient certificate. It is
not an end-to-end Lean theorem, a new global extremal bound, or a final review.

## Statement and dependencies

Let F be a finite simple family of four-element sets containing no three distinct
members with equal pairwise intersections, including empty intersection. Suppose
a point x has degree twenty. Import the universal SF3 bound twenty, its
degree-twenty equality classification, the intersecting SF3 bounds and separation
lemma B4, and the universal separated-C5 obstruction from the pinned upper-68
source. Then, if F has a member contained in one of the two six-point components
of the link of x, |F| is at most 67.

The classification writes the complete link as P10(Y) disjoint-union P10(Z),
where Y={0,...,5}, Z={6,...,11}, and the P10 blocks on Y are

    012 015 023 034 045 124 134 135 235 245.

The link on Z is the translate by six. The rest of the ambient ground set is
unrestricted. The theorem does not assume mu>=41, H27, a minimum positive degree,
an upper bound on the support, or any of the old mu42 bootstrap conclusions.
It does retain the imported universal structural theorems, whose complete Lean
formalization is not asserted here.

The source is the frozen clone under
`work/frontier20261020/prior-art68/repository/companion/upstream/`:
`MU42/TRACE_FOUNDATIONS.md` (especially D.1 and E), and `D20/PROOF.md` section 1.2.
The former explicitly states that its trace arguments assume no neighbourhood
threshold or support cutoff. The C5 argument in the latter precedes the removal
of internal members and gives d(y)-I_y<=15, where I_y counts members contained
in y's six-point component and containing y.

P10 has sixty automorphisms, transitive on its fifteen four-subsets. Together
with interchange of Y and Z, these normalize any internal member to M=0123.
This finite symmetry fact is a source dependency; a separate tiny orbit check
is recorded with the certificate. No completion is assumed symmetric.

## A local inequality requiring no neighbourhood hypothesis

Use the actual anchor R={x,1,3,5}. Among members avoiding x, write a,b,c for
the exact pair traces 13,15,35 on R; e for exact triple135; and s,t for exact
singletons1,3. The twenty prescribed cones contribute degree five at each
of 1 and 3. Hence

    d1=5+a+b+e+s,  d2=5+a+c+e+t.

The universal exact-trace bounds give a,b,c<=3, e<=1, s,t<=10 and d1,d2<=20.
The universal high-link decomposition (paper/main.tex:612–636,
lem:r16maximal) at degree at least eighteen gives
s<=7 => d1<=17 and t<=7 => d2<=17.
If s>=8, source D8 gives a,b<=2; if t>=8 it gives a,c<=2.

If both singletons are large, then e=0 and a<=1. Indeed the central index x
is large with k_x=10; its three exterior extension points are distinct.
If e=1, D9 applied between x and each of 1,3 would identify their extension
points, contrary to that distinction. If a=2, D9 between 1 and 3 would also
identify two of those points. Values a=3 are already excluded by D8.
Finally d1=20 forces (s,k1)=(10,10), so a=b=2 and e=1; symmetrically
d2=20 forces a=c=2 and e=1.

These elementary consequences imply

    W=3a+2b+2c+3e+2s+2t <= 51.                 (L51)

For clarity, W=2(d1+d2)-20-a-e as an integer identity. When both s,t are
at least eight, direct substitution of their bounds gives W<=51. When both
are at most seven, d1+d2<=34 and W<=48. In the mixed case s>=8,t<=7,
d2<=17. If d1<=18, W<=50. If d1=19, the bounds b<=2,s<=10 imply a+e>=2,
so W<=50. If d1=20 then a+e=3, so W<=51. The opposite mixed case is symmetric.
This proves L51 independently of a floating-point linear program or a signature
catalogue. A separate Lean arithmetic leaf may verify this implication; it does
not by itself formalize its geometric premises.

## Weighted incidence certificate

Put R=F minus the twenty members containing x and r=|R|. For Q in R use its
exact trace S=Q intersect (Y union Z). Although distinct Q can have the same
trace, incidence sums retain their multiplicities. There are only
sum_{j=0}^4 binomial(12,j)=794 possible traces.

Use the following upper bounds on counts of residual members, with the stated
weights. A central anchor abc means the actual member {x,a,b,c}; exact traces
therefore do not contain x.

| Row | Weight | Upper bound |
|---|---:|---:|
| Incidence of pair02 | 5 | 4 |
| Incidence of each of the ten P10 triples on Z | 5 each | 1 each |
| Exact singleton1 on central anchor012 | 2 | 10 |
| Exact pair05 on015,04 on034,04 on045,05 on045,24 on124,24 on245,25 on245 | 3,3,2,2,3,2,2 | 3 each |
| Exact singleton3 on M=0123 | 2 | 10 |
| Residual degree minus I_y, y=1 and y=3 | 1 each | 10 each |
| L51 on central anchor135 | 1 | 51 |
| Exact pair25 on central anchor235 | 3 | 3 |

The global pair bound is six, of which two are prescribed cones. The global
triple bound is two, of which one is a cone. The exact-trace bounds are the
universal intersecting residual capacities 10,3,1; any prescribed cones in an
exact class could only reduce its allowed residual count, so the displayed
weaker bounds remain valid. The C5 row is 15 minus the five prescribed cones.
The weighted right-hand side is exactly

    20+50+20+51+20+20+51+9 = 241.

Let q(S) be the total coefficient of a residual with trace S. Its explicit
integer formula is in `check_internal_certificate.py`. A trace S is excluded
whenever a link block T satisfies S intersect T = S intersect M = T intersect M:
the corresponding cone xT, M, and Q would be three distinct sunflower members.
Distinctness holds since x belongs only to the cone; S=M does not satisfy any
such exclusion because |T|=3<4. Unknown exterior points change none of these
three intersections.

The checker enumerates all 794 traces. Exactly 372 have a displayed blocking
cone. For the 422 remaining traces, its coefficient histogram is

    q=5:357, q=6:14, q=8:1, q=10:35, q=15:14, q=17:1.

In particular q(S)>=5 for every actual residual and q(M)=8. Since M is an
actual residual, summing gives 5r+3 <= sum_Q q(S(Q)) <=241. Thus r<=47 and
|F|=20+r<=67. Multiplicities of proper traces and arbitrary exterior supports
are fully covered by this argument.

## Assurance and next obligation

`internal_certificate.json` records the exact finite enumeration, row sum and
checker hash. Its arithmetic uses only Python integers, no solver, floating
point, source catalogue, or numerical library. This is certificate-diagnostic
evidence, not Lean kernel replay. The ordinary proof above exposes exactly
which imported universal geometry supports those rows.

For a hypothetical family of size68, all thirty internal members can therefore
be removed from subsequent relaxations, and every point in Y union Z has degree
at most fifteen. Excluding all degree-twenty families still requires the six
external marker cases. Global M(4,3)<=67 additionally requires the other maximum
degree cases. Neither conclusion is claimed here.
