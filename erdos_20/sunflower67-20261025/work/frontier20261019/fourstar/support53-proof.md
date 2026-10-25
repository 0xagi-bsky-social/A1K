# Four-star refinement: actual support at most 53

Mathematical proof for review, not yet a fully assembled Lean theorem. Derived prospectively after the three-star 56 bound; no global novelty claim. Same hypotheses: intersecting, 28 distinct four-sets, no three-sunflower, empty core allowed. Inherited bounds d1<=19, d2<=6, d3<=2.

Write n=|support|, P=sum_v binom(d_v,2), W=P-378. Assume n>=54, so s=sum_v(d_v-1)=112-n<=58. Choose four distinct top-degree supported points with a>=b>=c>=d>=1. Tail degrees are at most d. As before,

2P <= U = 58d+(a-d)(a-1)+(b-d)(b-1)+(c-d)(c-1).

Two-star and three-star union bounds give a+b<=34 and a+b+c<=46. Put D=a+b+c+d. For a member containing j of the four selected points, binom(j,2)>=2j-3 for j=0,1,2,3,4. Summing, the six selected pair-codegrees have sum S>=2D-84. Each is at most six, so S<=36 and D<=60. The simpler inequality binom(j,2)>=j-1 also gives S>=D-28. Put L=max(0,D-28), so S>=L.

For any two distinct members A,B with nonempty intersection I, put j=|I intersect chosenFour|. The pointwise inequality

|I|-1 >= binom(j,2)-binom(j,3)

holds for j=0..4 (and in fact for all nonnegative j when I is nonempty). Summing over unordered distinct member pairs yields

W >= sum_(6 pairs) binom(codegree,2) - sum_(4 triples) binom(triplecodegree,2)
  >= sum_(6 pairs) binom(codegree,2)-4.

Cauchy for the six pair-codegrees gives

12 sum binom(codegree,2) >= S^2-6S >= L^2-6L.

The last inequality uses monotonicity when L>=6; for 0<=L<=5 the desired inequality follows directly from nonnegativity of the binomial sum (do not claim S^2-6S>=L^2-6L in this small-L case). Hence

12P >= 4488+L^2-6L.

Combining requires

6U-L^2+6L >=4488.

An exact integer check on 1<=d<=c<=b<=a<=19, a+b<=34, a+b+c<=46, D<=60 gives maximum4475 at (19,14,13,13), L31,U875. Thus contradiction, proving n<=53. The diagnostic enumerates6031 admissible sortedquadruples.

A smaller kernel-checkable numerical leaf is possible. For fixed A=a+b+c<=46 and d in[1,min(c,60-A)], f(d)=6U-max(0,A+d-28)^2+6max(0,A+d-28) is increasing. Below A+d=28 its slope is 6(61-A)>0. Above the break its derivative (or integer finite difference) is 428-8A-2d, at least22 for A<=46,d<=19. The functions agree at the break. Therefore maximize at d=min(c,60-A), reducing the numerical leaf to Fin20^3. This monotonicity bridge must be proved if only the reduced grid is kernel-checked.

No I27 exclusion is established: the remaining finite obstruction now has capacity53 in the mathematical reduction, while the fully assembled Lean capacity remains72. No ProfileA/B exclusion or new f(4,3) bound follows. A four-star universal correction, rather than the compiled three-star correction alone, underlies this refinement.
