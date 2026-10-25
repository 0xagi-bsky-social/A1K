# Direct A3 image for the cap15 closure

24 October 2026. Additive ordinary simplification. The frozen complete
assembly and fibre notes remain unchanged. This replaces their initial
k=4 and empty-fibre reduction with the already imported theorem at k=3;
all later star-support and cover arguments are unchanged.

Let G be the disjointness graph of the hypothetical68-member family
after the proved N(Q)<=43 bound. Then G is triangle-free, has minimum
degree at least25, and has independence number at most27 by H27.

The exact imported Jin theorem in the pinned prior `paper/main.tex`,
lines169–175, gives a homomorphism to A_k whenever

    delta(G) > (k+1)|G|/(3k+2),  1<=k<=9.

Apply it directly at k=3, because25*11=275>4*68=272. Thus G maps to
the cyclic A3 on indices modulo8 with adjacency differences3,4,5.
Surjectivity is not assumed at this stage.

Write a_i>=0 for the eight fibre sizes, sum a_i=68, and put

    b_i=a_(i+3)+a_(i+4)+a_(i+5).

The three image neighbours of any index i are an independent set in
A3. Their full preimage is therefore independent in G, even when
fibre i is empty. Consequently b_i<=27 for every i. Set e_i=27-b_i.
Each e_i is nonnegative and

    sum b_i=3*68=204,  sum e_i=8*27-204=12.

The cyclic incidence identity is

    b_i+b_(i+3)+b_(i+5)=68+a_i.

Indeed the three expansions count every fibre once and fibre i twice.
It follows that

    a_i=13-e_i-e_(i+3)-e_(i+5)>=13-sum e_i=1.

Thus every image fibre is occupied, as a consequence of the mass and
independence bounds alone. For an actual graph vertex in fibre i,
all its graph neighbours lie in the three adjacent fibres. Hence
b_i>=delta(G)>=25. Now r_i=b_i-25 satisfies exactly the domain used
in the existing closing argument:

    r_i in {0,1,2},  sum r_i=4,
    a_i=7+r_i+r_(i+3)+r_(i+5).

This proves the same A3 interface without deleting any empty image
fibre, invoking a minimal-image theorem, or excluding A1,A2,A4
separately. It also makes the order of the lower-bound argument
explicit: b_i<=27 holds before surjectivity, while b_i>=25 is used
only after a_i>=1 has been established.

The argument uses only graph-homomorphism implications. It does not
assume a complete blowup. The independent/nonindependent star-support
analysis and the actual one/two-cone deletion-cover counts therefore
apply exactly as recorded in the existing cap15 closure.

Inspected sources:

| Source | SHA256 |
|---|---|
| Frozen prior paper/main.tex | 4aa36c9d56af5a8e3bdb44749107820549a73e0d3405e6c700104fa4c30e5c21 |
| LOW15-complete-argument.md | 6c3438b2ae2f8438b3c761019e3d1e711d13cf92679c082a7f33c8a762167b68 |
| LOW15-A3-star-fibre-reduction.md | 0b088edeecd0a486f19050422b446d871e31b87fc4098994f5aa1241f665455c |

The prior checkout is commit
`90c03c79bcf44eb8f61dff1b86091b822cc4cd3c`. This is a direct use of
its stated Jin theorem, not a new literature or priority claim. No
numerical process, finite enumeration, or Lean job is needed here.
