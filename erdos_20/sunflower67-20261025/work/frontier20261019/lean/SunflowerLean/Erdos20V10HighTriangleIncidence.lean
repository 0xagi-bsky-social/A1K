import SunflowerLean.Erdos20V10HighTriangleDegreeOne

namespace Erdos20V10HighTriangle
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20V8Boundary Erdos20DegreeCongruences Erdos20V9HighGraph
open Erdos20V9HighCompatibility Erdos20ExtremalTwenty

/-- A high point has at least eleven low neighbors because at most one of its
twelve point-link support points can be high. -/
theorem high_point_low_neighbors_ge_eleven {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) :
    11 ≤ (support (residualLink F {x}) \ highPoints F).card := by
  let L := residualLink F {x}
  have huL : ∀ P ∈ L, P.card=3 := by simpa using residualLink_uniform (core := ({x} : Finset α)) hu
  have hfL : IsSunflowerFree L 3 := residualLink_sunflowerFree hf
  have hcL : L.card=20 := by simpa [L,card_residualLink,upperStar,degree] using (Finset.mem_filter.mp hx).2
  have hs := (extremal_twenty_regular_twelve L huL hfL hcL).1
  have h1 := high_point_high_neighbors_le_one F hu hf x hx
  have he := Finset.card_sdiff_add_card_inter (support L) (highPoints F)
  change (support L ∩ highPoints F).card ≤ 1 at h1
  change 11 ≤ (support L \ highPoints F).card
  omega

/-- Improved unconditional high-low incidence capacity. -/
theorem eleven_mul_high_card_le_four_mul_low_card {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3) :
    11*(highPoints F).card ≤ 4*(support F \ highPoints F).card := by
  calc
    _ = ∑ _x ∈ highPoints F, 11 := by simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ highPoints F, (support (residualLink F {x}) \ highPoints F).card :=
      Finset.sum_le_sum (fun x hx => high_point_low_neighbors_ge_eleven F hu hf x hx)
    _ = ∑ y ∈ support F \ highPoints F, (highNeighbors F y).card := high_low_incidence_identity F
    _ ≤ ∑ _y ∈ support F \ highPoints F, 4 := Finset.sum_le_sum
      (fun y hy => low_point_high_neighbors_le_four F hu hf (member_high_points_card_le_two F hu hf)
        y (Finset.mem_sdiff.mp hy).2)
    _ = _ := by simp [Nat.mul_comm]

end Erdos20V10HighTriangle
