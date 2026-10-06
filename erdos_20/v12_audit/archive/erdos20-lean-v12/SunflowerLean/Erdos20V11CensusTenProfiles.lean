import SunflowerLean.Erdos20V11Census

namespace Erdos20V11Census
open Erdos20V8Boundary Erdos20BCWConditional Erdos20DegreeCongruences Erdos20V9Census

/-- The ten numerical degree profiles surviving the at-most-two-high-point
restriction; no profile is asserted to be realizable. -/
def TenCensusProfiles (a b c d : ℕ) : Prop :=
    (a=0 ∧ b=0 ∧ c=16 ∧ d=1) ∨
    (a=0 ∧ b=1 ∧ c=14 ∧ d=2) ∨
    (a=1 ∧ b=16 ∧ c=1 ∧ d=0) ∨
    (a=2 ∧ b=14 ∧ c=2 ∧ d=0) ∨
    (a=2 ∧ b=15 ∧ c=0 ∧ d=1) ∨
    (a=3 ∧ b=12 ∧ c=3 ∧ d=0) ∨
    (a=3 ∧ b=13 ∧ c=1 ∧ d=1) ∨
    (a=4 ∧ b=10 ∧ c=4 ∧ d=0) ∨
    (a=4 ∧ b=11 ∧ c=2 ∧ d=1) ∨
    (a=4 ∧ b=12 ∧ c=0 ∧ d=2)

/-- Exact arithmetic reduction from the four-class census to ten profiles. -/
theorem ten_census_profiles_arithmetic
    (a b c d : ℕ) (hs : a+b+c+d=17 ∨ a+b+c+d=18) (ha : a≤4)
    (ht : 17*a+18*b+19*c+20*d=324) (hd : d≤2) (hp : 1≤c+d) :
    TenCensusProfiles a b c d := by
  interval_cases d <;> interval_cases a <;> simp_all [TenCensusProfiles] <;> omega

/-- Family-level arithmetic bridge, leaving only the high-cardinality bound
as a separate geometric input. -/
theorem conditional_eighty_one_ten_profiles_of_high_card_le_two
    (hI : Erdos20V8Targets.IntersectingRankFourUpper 27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R∈F, R.card=4) (hf : IsSunflowerFree F 3) (hc : F.card=81)
    (hd : (highPoints F).card≤2) :
    TenCensusProfiles (degreeClass F 17).card (degreeClass F 18).card
      (degreeClass F 19).card (highPoints F).card := by
  obtain ⟨hs,ha,ht,_,hp⟩ := conditional_eighty_one_census hI F hu hf hc
  exact ten_census_profiles_arithmetic _ _ _ _ hs ha ht hd hp

end Erdos20V11Census
