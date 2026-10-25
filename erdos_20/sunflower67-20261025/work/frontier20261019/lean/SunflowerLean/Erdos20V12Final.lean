import SunflowerLean.Erdos20V12HighCardTwo
import SunflowerLean.Erdos20V12ProfileReduction
import SunflowerLean.Erdos20V12Intersecting

namespace Erdos20V12Final
open Erdos20BCWConditional Erdos20DegreeCongruences Erdos20V8Boundary
open Erdos20V9Census Erdos20V12Profile Erdos20V8Targets

/-- A consolidated conditional81 boundary with precisely the two remaining
necessary degree profiles. The intersecting ceiling remains explicit. -/
theorem conditional_eighty_one_boundary_rigidity
    (hI : IntersectingRankFourUpper 27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3) (hc : F.card=81) :
    (support F).card=17 ∧ degreeClass F 17=∅ ∧
    TwoCensusProfiles (degreeClass F 18).card (degreeClass F 19).card (highPoints F).card ∧
    (highPoints F).card≤2 ∧ (∀ R ∈ F, (R ∩ highPoints F).card≤1) := by
  obtain ⟨hs,h17,hp⟩ := conditional_eighty_one_two_profiles hI F hu hf hc
  exact ⟨hs,h17,hp,Erdos20V12HighCard.high_points_card_le_two F hu hf,
    (Erdos20V11Final.conditional_eighty_one_boundary_rigidity hI F hu hf hc).2.2.2⟩

/-- Statement fidelity: the two remaining tuples are literal exact counts. -/
theorem two_profiles_literal (b c d : ℕ) :
    TwoCensusProfiles b c d ↔ ((b=0 ∧ c=16 ∧ d=1) ∨ (b=1 ∧ c=14 ∧ d=2)) := Iff.rfl

end Erdos20V12Final
