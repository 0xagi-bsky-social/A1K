# Top-three-star support reduction: 85 to 56

## General three-star correction (independent reusable statement)

For **any** finite intersecting r-uniform family F of m distinct sets, with point
degrees d_v, choose three distinct ground points x,y,z. Let c_xy,c_xz,c_yz be
their pair-codegrees and t their common triple-codegree. Then

    sum_v d_v^2 >= m*(m+r-1)
      + c_xy*(c_xy-1) + c_xz*(c_xz-1) + c_yz*(c_yz-1)
      - t*(t-1).                                          (G)

No sunflower hypothesis or upper degree/codegree bound enters (G), so unlike the
28-member obstruction specialization this universal statement has numerous
nonempty instances. It is an exact correction to the usual intersecting
second-moment bound. No claim of global mathematical novelty is made.

Here is a direct proof that also describes an economical formalization. Set
C={x,y,z} and, for any nonempty finite set I, define

    k(I)=|I| + 1[C subset I]
      - 1[{x,y} subset I] - 1[{x,z} subset I] - 1[{y,z} subset I].

If j=|I intersect C|, its subtracted correction is binom(j,2)-binom(j,3),
which equals 0,0,1,2 for j=0,1,2,3. Therefore k(I)>=1 for every nonempty I.
Apply this to every ordered pair of **different** members S,T. Retain the
diagonal exactly: k(S)=r+1[C subset S]-sum_pair 1[pair subset S]. Thus

    sum_{S,T in F} k(S intersect T)
      >= m*(m-1)+m*r+t-c_xy-c_xz-c_yz.

The left side is sum_v d_v^2+t^2-c_xy^2-c_xz^2-c_yz^2, by double counting.
Rearrangement proves (G). It also covers m=0,1 and arbitrary nonnegative rank,
with intersectingness interpreted literally as in A1K; the empty-family case is
vacuous. Distinctness of the chosen points is necessary for the stated k-table.

The current `Support56.lean` formalization includes the generic diagonal-sum
lemma, the fixed-m=28,r=4 calculation, and the general statement named
`FrontierSupport56.three_star_second_moment`. Its compiler status must be read
from the actual last successful receipt, not from this draft.

## Specialization and finite-support consequence

Status: complete mathematical draft of the universal reduction; finite numerical
leaf checked separately in `SupportGrid.lean` when its compiler receipt succeeds.
The set-family-to-moment bridges are not thereby Lean checked. No new bound on the
maximum size of a sunflower-free family is claimed. Novelty is asserted only as a
candidate strengthening of A1K's shipped finite-support reduction; broader
literature novelty is unestablished. The published computational I(27) theorem
of Axante et al. remains a separate result and does not enter the argument.

**Statement.** If F is an intersecting 28-member family of distinct four-element
sets, containing no three-member sunflower (empty core included), then its actual
support has size at most 56. This concerns the actual support, not a quotient or
point-identification compression.

Write n for support size and d_v for point degrees. The shipped A1K theorem
`Erdos20ExtremalTransversals.intersecting_rank_four_card_ge_twenty_one_degree_le_nineteen`
gives d_v<=19. The pair-codegree bound is <=6. A triple-codegree is <=2: three
distinct four-sets containing the same triple would have distinct fourth points
and form a sunflower with that triple as core. These are the only sunflower
inputs used below.

Let

    P = sum_v binom(d_v,2),     W=P-binom(28,2)=P-378.

Counting incidences gives sum_v d_v=112. Counting ordered-free pairs of members
through their shared points gives P=sum_{A<B}|A intersect B|. Since F is
intersecting, W=sum_{A<B}(|A intersect B|-1)>=0.

Assume n>=57. Choose three points of highest degrees a>=b>=c. There are at least
three support points. Every remaining point has degree in [1,c]. Put s=112-n,
so s<=55. From d(d-1)<=c(d-1) on those remaining points,

    2P <= a(a-1)+b(b-1)+c(c-1)+c*(s-a-b-c+3)
       <= U := 55c+(a-c)(a-1)+(b-c)(b-1).                  (1)

The expression s-a-b-c+3 is exactly the sum of (d_v-1) over all remaining
points, hence nonnegative. Only the final replacement of s by 55 uses n>=57.

Let x,y,z be the pair-codegrees of the three chosen points, and t their common
triple-codegree. Then 0<=x,y,z<=6 and 0<=t<=2. Inclusion-exclusion for their
three point-stars gives

    a+b+c-x-y-z+t <= 28.

Consequently a+b<=34 (using the two-star union), a+b+c<=46, and

    x+y+z >= L := max(0,a+b+c-28).                         (2)

For each pair of members A<B, let j be how many of the selected three points
lie in A intersect B. Since |A intersect B| is between one and three,

    |A intersect B|-1 >= binom(j,2)-binom(j,3).

Summing this inequality and double-counting produces

    W >= binom(x,2)+binom(y,2)+binom(z,2)-binom(t,2)
      >= binom(x,2)+binom(y,2)+binom(z,2)-1.              (3)

The subtraction of one is essential; simply subtracting all pair overlap
counts would overcharge a pair of members sharing all three selected points.

The elementary sum-of-squares inequality gives

    6*(binom(x,2)+binom(y,2)+binom(z,2))
      =3*(x*x+y*y+z*z)-3*(x+y+z)
      >= (x+y+z)^2-3*(x+y+z)
      >= L*L-3*L.                                        (4)

For L>=3, the last step is monotonicity on integers >=L. For L=0,1,2 the
desired inequality follows directly from nonnegativity of the left side.
Combining (3), (4), and P=W+378 yields

    6P >= 2262+L*L-3*L.                                 (5)

Equations (1) and (5) require

    3U-L*L+3*L >= 2262.                                 (6)

It remains only to check the finite range

    1<=c<=b<=a<=19, a+b<=34, a+b+c<=46.

Over this range the maximum of the left side in (6) is exactly 2250, attained
at (a,b,c)=(16,15,15), with L=18 and U=840. The kernel-checkable numerical
statement `FrontierSupportGrid.grid_bound` asserts its upper bound 2250 on
the entire Fin20^3 grid, under precisely these inequalities. Thus (6) is
impossible, with margin twelve, proving n<=56.

## Explicit remaining formalization obligations

1. Choose three distinct top-degree supported points, preserving the sorted
   ordering and the tail-degree bound.
2. Prove the tail degree-envelope inequality (1) via finite sums and the degree
   sum 112.
3. Connect the general ordered-pair correction to the arithmetic specialization,
   including the t<=2 bound. `Support56.lean` contains the general correction
   and the triple-codegree helper; its final compile receipt decides their grade.
4. Establish inclusion-exclusion (2), the integer sum-of-squares bound (4), and
   apply the independently checked finite numerical leaf.
5. Reuse A1K's injective relabeling bridge to replace Fin85 by Fin56 in the exact
   obstruction equivalence, after the universal support theorem is elaborated
   and its axiom closure audited.

The existing A1K sources have a Fin85 support bound and do not contain this
top-three-star correction in the inspected file names/declarations. The known
computer-assisted proof of I(27) makes the hypothetical 28-member class empty
in ordinary mathematics; this reduction is useful as a smaller independent
finite proof target and is not a claim to improve that published extremum.
