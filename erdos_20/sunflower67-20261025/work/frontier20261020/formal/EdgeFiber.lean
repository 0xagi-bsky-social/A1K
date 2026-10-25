import SunflowerLean.Erdos20CrossBounds

namespace FrontierEdgeFiber
open Erdos20CrossBounds Erdos20Incidence

/-- A sunflower-free graph has maximum degree two, so on a prescribed
finite vertex set its edge count is at most its vertex count. -/
theorem rank_two_on_universe_card_le
    {α : Type*} [DecidableEq α] (G : Finset (Finset α)) (U : Finset α)
    (hu : ∀ P ∈ G, P.card = 2) (hf : IsSunflowerFree G 3)
    (hsub : ∀ P ∈ G, P ⊆ U) : G.card ≤ U.card := by
  have hinc := incidence_sum_eq G U
  have hl : (∑ P ∈ G, (P ∩ U).card) = 2 * G.card := by
    calc
      _ = ∑ _P ∈ G, 2 := Finset.sum_congr rfl (fun P hP => by
        rw [Finset.inter_eq_left.mpr (hsub P hP),hu P hP])
      _ = _ := by simp [Nat.mul_comm]
  have hr : (∑ x ∈ U, (G.filter (fun P => x ∈ P)).card) ≤ 2 * U.card := by
    calc
      _ ≤ ∑ _x ∈ U, 2 := Finset.sum_le_sum (fun x _ =>
        rank_two_three_petals_degree_le_two G hu hf x)
      _ = _ := by simp [Nat.mul_comm]
  omega

/-- The outside-pair fiber bound used in the Profile A argument. -/
theorem rank_two_on_four_points_card_le_four
    {α : Type*} [DecidableEq α] (G : Finset (Finset α)) (U : Finset α)
    (hu : ∀ P ∈ G, P.card = 2) (hf : IsSunflowerFree G 3)
    (hsub : ∀ P ∈ G, P ⊆ U) (hU : U.card = 4) : G.card ≤ 4 := by
  simpa only [hU] using rank_two_on_universe_card_le G U hu hf hsub

end FrontierEdgeFiber
