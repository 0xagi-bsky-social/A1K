# A complete R16 link with one outer triple deleted is impossible at cap15

24 October 2026. Ordinary proof development in the existing Oct23 work
directory. This is an incidence argument on an explicitly supplied link;
it does not assume that every size15 link has this form. No solver,
classification enumeration or Lean compilation was run.

## Statement

Let F be a finite simple sunflower-free four-uniform family with |F|=68
and maximum point degree at most15. Suppose every actual member has
neighbourhood size at least41, and every exact singleton pool at every
actual member has size at most8.

Then no point x has a complete link isomorphic to R16 with one outer
hub-plus-triad-edge triple removed.

The neighbourhood lower bound follows from H27. The global singleton
bound is available in the cap15 branch after the ordinary no-P10 and
no-P9 arguments. Neither a neighbourhood upper bound nor the rho7
classification is needed for this lemma.

## Complete-link model and residual traces

Let K={u,v,a,b} be the four distinct hubs and let D,E be disjoint triads,
all ten points distinct. The R16 triple family is

    {u+P,v+P : P in binom(D,2)}
      union binom(K,3)
      union {a+P,b+P : P in binom(E,2)}.

An outer triple means one from the first or last part, containing one
hub and two triad points. Assume that the complete x-link is this
family minus one such triple. In particular d(x)=15, all four hub
triples K minus i remain, and the sum of the hub degrees in the link
is23: it was24 in R16 and the deletion removes one hub incidence.

Remove the15 members through x and count exact traces of the remaining
family on K. Let s_i count trace {i}, p_ij trace {i,j}, t_i trace K minus i,
and q trace K. Put

    S=sum_i s_i, P=sum_(i<j) p_ij, T=sum_i t_i,
    E0=S+P+T+q.

The symbol E0 counts residual members meeting K; it does not refer to
the named triad E. No restriction is placed on the exterior points of
these members, and members disjoint from K are allowed. All counts are
nonnegative integers.

## Four actual neighbourhood inequalities

For each i in K the member Q_i={x} union (K minus i) is actual. Every
member through x meets Q_i. A residual member meeting K misses Q_i
exactly when its trace is {i}. Hence, without an inequality loss,

    N(Q_i)=15+E0-s_i.

Since each N(Q_i)>=41, summing gives

    4*E0-S=3*S+4*P+4*T+4*q>=104.                 (1)

The total global degree of the four hubs is at most60. The15 x-cones
already contribute23 to that total. Residual hub incidences therefore
satisfy

    S+2*P+3*T+4*q<=37.                          (2)

Subtracting the left side of (1) from three times the left side of
(2), and using their respective lower and upper bounds, yields

    2*P+5*T+8*q<=111-104=7.                    (3)

In particular q=0 and T<=1; when T=0 one has P<=3, and when T=1 one
has P<=1.

## Singleton capacities at the actual hub anchors

For distinct i,j in K, the exact singleton-i pool at Q_j is precisely
the residual members whose trace on K is {i} or {i,j}. Indeed Q_j
contains x and every hub except j, and all members containing x meet
it at x. Thus the assumed singleton bound gives

    s_i+p_ij<=8                              (i!=j).       (4)

Consequently every s_i<=8 and S<=32. If P>0, choose an actual positive
pair count p_ij>=1. Applying (4) in both directions gives s_i,s_j<=7,
and therefore S<=30.

If P=0, equations (3) and q=0 give T<=1, so the left side of (1) is
at most3*32+4=100, below104.

If P>0 and T=0, use P<=3 and S<=30 to bound that left side by
3*30+4*3=102. If P>0 and T=1, use P<=1 and S<=30 to bound it by
3*30+4+4=98. Both contradict (1).

These cases exhaust (3), proving the statement.

## Consequence and exact scope

The ordinary theorem in `LOW15-R15-rho7-classification.md` classifies
a size15 SF3 link with rho exactly7 as R16 with one triple removed.
Combining that theorem with the present lemma leaves only deletion
of a hub triple in any such complete point-link in the cap15 family.
This conclusion uses the supplied rho7 guard; it does not classify
size15 links with rho<=6, or exclude the hub-deletion type.

The classification note has SHA256
`151e0cde17bdf12f3ab348248a47d721edadc23baf6aee8e32aeacb0971056e6`.
The global singleton8 route is `LOW15-NO9-fibre-route.md`, SHA256
`576a463ffc3c86138e53d6919f75ead7274a6dd46401a69bc3b6ca8e3b41e0b1`,
following the prior no-P10 argument. The four inequalities above are
proved directly for actual members and arbitrary exterior multiplicities;
no finite support cutoff or conditional model feasibility is used.
