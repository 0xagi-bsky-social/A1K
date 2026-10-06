import SunflowerLean.Erdos20V9Final

namespace Erdos20V9Consequences
open Erdos20StrictCore Erdos20BCWConditional Erdos20Incidence
open Erdos20V9Final Erdos20V8Targets

/-- Expanded public statement: the intersecting premise and unrestricted conclusion
quantify over arbitrary finite families in every small ambient type. -/
theorem literal_conditional_eighty_one
    (hI : ∀ {β : Type} [DecidableEq β] (G : Finset (Finset β)),
      (∀ S ∈ G, S.card=4) → IsSunflowerFree G 3 →
      (∀ S ∈ G, ∀ T ∈ G, (S ∩ T).Nonempty) → G.card≤27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card=4) (hf : IsSunflowerFree F 3) : F.card≤81 := by
  exact unrestricted_upper_eighty_one_of_intersecting_twenty_seven hI F hu hf

/-- The conditional rank-four seed improves the refined rank-five consequence. -/
theorem rank_five_le_eight_hundred_two_of_intersecting_twenty_seven
    (hI : IntersectingRankFourUpper 27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 5) (hf : IsSunflowerFree F 3) : F.card ≤ 802 := by
  have hd : ∀ x, (F.filter (fun S => x ∈ S)).card ≤ 81 := by
    intro x
    have hb := unrestricted_upper_eighty_one_of_intersecting_twenty_seven hI
      (residualLink F {x})
      (by simpa using residualLink_uniform (core := {x}) hu)
      (residualLink_sunflowerFree hf)
    simpa [card_residualLink,upperStar] using hb
  have hb := card_le_refined_step F 5 3 81 (by decide) (by decide) hu hf hd
  exact hb

/-- One further refined incidence step at rank six, with the same explicit premise. -/
theorem rank_six_le_nine_thousand_six_hundred_fourteen_of_intersecting_twenty_seven
    (hI : IntersectingRankFourUpper 27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 6) (hf : IsSunflowerFree F 3) : F.card ≤ 9614 := by
  have hd : ∀ x, (F.filter (fun S => x ∈ S)).card ≤ 802 := by
    intro x
    have hb := rank_five_le_eight_hundred_two_of_intersecting_twenty_seven hI
      (residualLink F {x})
      (by simpa using residualLink_uniform (core := {x}) hu)
      (residualLink_sunflowerFree hf)
    simpa [card_residualLink,upperStar] using hb
  have hb := card_le_refined_step F 6 3 802 (by decide) (by decide) hu hf hd
  exact hb

end Erdos20V9Consequences
