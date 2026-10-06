import SunflowerLean.Erdos20TracePatterns
import SunflowerLean.Erdos20DesignConsequences
import SunflowerLean.Erdos20RankFour
import SunflowerLean.Erdos20RankFourWitness
import SunflowerLean.Erdos20GrowthRate

/-! Unconditional assembly of the version-five structural and finite-rank results.
The finite-growth hypothesis in the separate limiting-rate interface is not discharged. -/
namespace Erdos20V5Frontier
open Erdos20BCWConditional Erdos20TracePatterns Erdos20DesignConsequences

/-- An intersecting extremal triple family is a simple two-(six,three,two) design. -/
theorem intersecting_ten_design {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 10) :
    (support F).card = 6 ∧
    (∀ x ∈ support F, (F.filter (fun S => x ∈ S)).card = 5) ∧
    (∀ x ∈ support F, ∀ y ∈ support F, x ≠ y →
      (F.filter (fun S => ({x,y} : Finset α) ⊆ S)).card = 2) := by
  obtain ⟨hs,hd⟩ := intersecting_ten_regular_six_support F hu hf hi hc
  exact ⟨hs,hd,fun x hx y hy hxy =>
    regular_six_pair_codegree_eq_two F hu hf hs hd x y hx hy hxy⟩

/-- No two-point set meets all members of an intersecting extremal triple family. -/
theorem intersecting_ten_no_two_point_transversal {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 10)
    (C : Finset α) (hC : C.card = 2) : ∃ S ∈ F, S ∩ C = ∅ := by
  obtain ⟨hs,hd⟩ := intersecting_ten_regular_six_support F hu hf hi hc
  exact regular_six_no_two_point_transversal F hu hf hc hs hd C hC

/-- Every supported pair meets exactly eight of the ten members. -/
theorem intersecting_ten_pair_meets_eight {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 10)
    (x y : α) (hx : x ∈ support F) (hy : y ∈ support F) (hxy : x ≠ y) :
    (F.filter (fun S => (S ∩ {x,y}).Nonempty)).card = 8 := by
  obtain ⟨hs,hd⟩ := intersecting_ten_regular_six_support F hu hf hi hc
  exact regular_six_pair_meeting_card_eq_eight F hu hf hs hd x y hx hy hxy

end Erdos20V5Frontier
