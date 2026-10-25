import SunflowerLean.Erdos20V8Boundary

namespace Erdos20V9BoundaryArithmetic

/-- No degree-class census satisfies the near82 boundary conditions. -/
theorem no_eighty_two_degree_census (a b c d : ℕ)
    (hc : 17*a + 18*b + 19*c + 20*d = 328)
    (ha : 17*a ≤ 82)
    (hsmall : 17*a + 18*b ≤ 164)
    (hedge : 10*d ≤ 4*(a+b+c)) : False := by
  have hs : 17 ≤ a+b+c+d ∧ a+b+c+d ≤ 18 := by omega
  have hd : d ≤ 5 := by omega
  omega

end Erdos20V9BoundaryArithmetic
