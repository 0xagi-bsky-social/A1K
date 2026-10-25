import Mathlib.Tactic

/-!
Arithmetic interfaces in the size-fifteen link argument. These theorems
check the stated inequalities only. Their geometric hypotheses, finite
classification predicates and arbitrary-support bridges are proved in the
separate ordinary notes; they are not silently supplied by this module.
-/
namespace FrontierR15

theorem outer_deletion_scalar_impossible
    (S P T q : ℕ)
    (anchors : 104 ≤ 3*S + 4*P + 4*T + 4*q)
    (budget : S + 2*P + 3*T + 4*q ≤ 37)
    (singletons : S ≤ 32)
    (positive_pairs : 0 < P → S ≤ 30) : False := by
  by_cases h : P = 0
  · omega
  · have hP : 0 < P := by omega
    have := positive_pairs hP
    omega

/-- The ordered deficit triangle with all three strict capacities. -/
theorem hub_strict_triangle_impossible
    (Y t a b c : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c)
    (upper : Y + 3*t ≤ 8)
    (lower : 1+b+c ≤ Y+t)
    (strict_pairs : Y+3 ≤ 2*a+b) : False := by
  omega

/-- All equality guards are kept as explicit hypotheses. Here p,q,r are
the three satellite pair counts, ordered by endpoint deficits a,b,c. -/
theorem hub_deletion_scalar_impossible
    (p q r t a b c : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c)
    (hp : p ≤ a) (hq : q ≤ a) (hr : r ≤ b)
    (upper : p+q+r+3*t ≤ 8)
    (lower : 1+b+c ≤ p+q+r+t)
    (guardp : p=a → q+t=0)
    (guardq : q=a → p+t=0)
    (guardr : r=b → p+t=0) : False := by
  have hpstrict : p+1 ≤ a := by
    by_contra hn
    have heq : p=a := by omega
    have hz := guardp heq
    omega
  have hqstrict : q+1 ≤ a := by
    by_contra hn
    have heq : q=a := by omega
    have hz := guardq heq
    omega
  have hrstrict : r+1 ≤ b := by
    by_contra hn
    have heq : r=b := by omega
    have hz := guardr heq
    omega
  exact hub_strict_triangle_impossible (p+q+r) t a b c hab hbc
    upper lower (by omega)

/-- The derived minimum-used-degree-three incidence bound forces support
at most eleven. I counts unordered intersecting pairs. -/
theorem rho_six_support_le_eleven
    (n I : ℕ) (pair_lower : 60 ≤ I)
    (incidence : 2*I + 14*n ≤ 285) : n ≤ 11 := by
  omega

theorem rho_six_requires_degree_five
    (I : ℕ) (pair_lower : 60 ≤ I)
    (degree_four_bound : 4*I ≤ 225) : False := by
  omega

#print axioms outer_deletion_scalar_impossible
#print axioms hub_strict_triangle_impossible
#print axioms hub_deletion_scalar_impossible
#print axioms rho_six_support_le_eleven
#print axioms rho_six_requires_degree_five

end FrontierR15
