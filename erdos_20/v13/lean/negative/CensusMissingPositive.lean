import SunflowerLean.Erdos20V13Boundary

example : 18*18+19*0+20*0 = (324 : ℕ) ∧ (0 : ℕ) ≤ 2 := by decide
-- Intended rejection: the positive degree-19-or-20 witness cannot be omitted.
theorem wrong_census_without_positive_witness :
    Erdos20V12Profile.TwoCensusProfiles 18 0 0 := by
  unfold Erdos20V12Profile.TwoCensusProfiles
  decide
