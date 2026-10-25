import Mathlib.Tactic

namespace FrontierMomentArithmetic

/-- The integer falling factorial of a nonnegative integer is nonnegative. -/
theorem falling_factorial_nonneg (x : ℤ) (hx : 0 ≤ x) :
    0 ≤ x * (x - 1) := by
  by_cases hzero : x = 0
  · simp [hzero]
  · have hone : 1 ≤ x := by omega
    exact mul_nonneg hx (by omega)

/-- The only possible triple codegrees are 0, 1, and 2. -/
theorem triple_correction_le_two (t : ℤ) (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    t * (t - 1) ≤ 2 := by
  interval_cases t <;> norm_num

/-- Moving the Cauchy lower bound from an actual sum to a smaller nonnegative
lower bound is valid even below the turning point of the quadratic. -/
theorem quadratic_lower_of_sum_bounds (k L S P : ℤ)
    (hk : 0 ≤ k) (hL : 0 ≤ L) (hLS : L ≤ S) (hP : 0 ≤ P)
    (hC : S * S - k * S ≤ k * P) :
    L * L - k * L ≤ k * P := by
  by_cases hLk : L ≤ k
  · have hp := mul_nonneg hk hP
    have hn := mul_nonneg hL (sub_nonneg.mpr hLk)
    nlinarith
  · have hm := mul_nonneg (sub_nonneg.mpr hLS)
        (show 0 ≤ S + L - k by omega)
    nlinarith

/-- Three pair codegrees and one triple codegree convert the corrected second
moment into the exact lower bound used for a 28-member obstruction. -/
theorem three_pair_moment_bound (Q L X Y Z T : ℤ)
    (hL : 0 ≤ L) (hLS : L ≤ X + Y + Z)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hT0 : 0 ≤ T) (hT2 : T ≤ 2)
    (hmoment : 868 + X * (X - 1) + Y * (Y - 1) + Z * (Z - 1) -
      T * (T - 1) ≤ Q) :
    2262 + L ^ 2 - 3 * L ≤ 3 * (Q - 112) := by
  let P := X * (X - 1) + Y * (Y - 1) + Z * (Z - 1)
  have hP : 0 ≤ P := by
    dsimp [P]
    linarith [falling_factorial_nonneg X hX, falling_factorial_nonneg Y hY,
      falling_factorial_nonneg Z hZ]
  have hC : (X + Y + Z) * (X + Y + Z) - 3 * (X + Y + Z) ≤ 3 * P := by
    dsimp [P]
    nlinarith only [sq_nonneg (X - Y), sq_nonneg (X - Z), sq_nonneg (Y - Z)]
  have hquad := quadratic_lower_of_sum_bounds 3 L (X + Y + Z) P
    (by norm_num) hL hLS hP hC
  have ht := triple_correction_le_two T hT0 hT2
  dsimp [P] at hquad
  nlinarith

/-- Six pair codegrees and four triple codegrees give the four-star lower bound. -/
theorem six_pair_moment_bound (Q L X₁ X₂ X₃ X₄ X₅ X₆ T₁ T₂ T₃ T₄ : ℤ)
    (hL : 0 ≤ L) (hLS : L ≤ X₁ + X₂ + X₃ + X₄ + X₅ + X₆)
    (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂) (hX₃ : 0 ≤ X₃)
    (hX₄ : 0 ≤ X₄) (hX₅ : 0 ≤ X₅) (hX₆ : 0 ≤ X₆)
    (hT₁0 : 0 ≤ T₁) (hT₁2 : T₁ ≤ 2)
    (hT₂0 : 0 ≤ T₂) (hT₂2 : T₂ ≤ 2)
    (hT₃0 : 0 ≤ T₃) (hT₃2 : T₃ ≤ 2)
    (hT₄0 : 0 ≤ T₄) (hT₄2 : T₄ ≤ 2)
    (hmoment : 868 + X₁ * (X₁ - 1) + X₂ * (X₂ - 1) +
      X₃ * (X₃ - 1) + X₄ * (X₄ - 1) + X₅ * (X₅ - 1) + X₆ * (X₆ - 1) -
      T₁ * (T₁ - 1) - T₂ * (T₂ - 1) - T₃ * (T₃ - 1) - T₄ * (T₄ - 1) ≤ Q) :
    4488 + L ^ 2 - 6 * L ≤ 6 * (Q - 112) := by
  let P := X₁ * (X₁ - 1) + X₂ * (X₂ - 1) + X₃ * (X₃ - 1) +
    X₄ * (X₄ - 1) + X₅ * (X₅ - 1) + X₆ * (X₆ - 1)
  let S := X₁ + X₂ + X₃ + X₄ + X₅ + X₆
  have hP : 0 ≤ P := by
    dsimp [P]
    linarith [falling_factorial_nonneg X₁ hX₁, falling_factorial_nonneg X₂ hX₂,
      falling_factorial_nonneg X₃ hX₃, falling_factorial_nonneg X₄ hX₄,
      falling_factorial_nonneg X₅ hX₅, falling_factorial_nonneg X₆ hX₆]
  have hC : S * S - 6 * S ≤ 6 * P := by
    dsimp [S, P]
    nlinarith only [sq_nonneg (X₁ - X₂), sq_nonneg (X₁ - X₃),
      sq_nonneg (X₁ - X₄), sq_nonneg (X₁ - X₅), sq_nonneg (X₁ - X₆),
      sq_nonneg (X₂ - X₃), sq_nonneg (X₂ - X₄), sq_nonneg (X₂ - X₅),
      sq_nonneg (X₂ - X₆), sq_nonneg (X₃ - X₄), sq_nonneg (X₃ - X₅),
      sq_nonneg (X₃ - X₆), sq_nonneg (X₄ - X₅), sq_nonneg (X₄ - X₆),
      sq_nonneg (X₅ - X₆)]
  have hquad := quadratic_lower_of_sum_bounds 6 L S P (by norm_num) hL hLS hP hC
  have ht₁ := triple_correction_le_two T₁ hT₁0 hT₁2
  have ht₂ := triple_correction_le_two T₂ hT₂0 hT₂2
  have ht₃ := triple_correction_le_two T₃ hT₃0 hT₃2
  have ht₄ := triple_correction_le_two T₄ hT₄0 hT₄2
  dsimp [P] at hquad
  nlinarith

#print axioms three_pair_moment_bound
#print axioms six_pair_moment_bound

end FrontierMomentArithmetic
