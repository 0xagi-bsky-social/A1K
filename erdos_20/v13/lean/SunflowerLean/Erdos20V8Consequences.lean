import SunflowerLean.Erdos20V8Final

namespace Erdos20V8Consequences
open Erdos20StrictCore Erdos20BCWConditional Erdos20RankThree Erdos20MeetingFiftySix Erdos20Incidence
open Erdos20V8Final Erdos20V8Targets

/-- The unconditional boundary result exposes an anchor meeting at most55 members. -/
theorem eighty_three_exists_anchor_meeting_le_fifty_five
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3) (hc : F.card = 83) :
    ∃ R ∈ F, (F.filter (fun S => (S ∩ R).Nonempty)).card ≤ 55 := by
  classical
  by_contra hn
  push_neg at hn
  apply no_eighty_three_all_meeting_fifty_six F hu hf hc
  intro R hR
  have hlo := hn R hR
  have hhi := meeting_neighborhood_card_le_fifty_six F R hR hu hf
  omega

/-- Any hypothetical83-member family contains an intersecting subfamily
of at least28 members. No external intersecting upper bound is used. -/
theorem eighty_three_contains_intersecting_twenty_eight
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3) (hc : F.card = 83) :
    ∃ G ⊆ F, 28 ≤ G.card ∧ (∀ S ∈ G, ∀ T ∈ G, (S ∩ T).Nonempty) := by
  classical
  obtain ⟨R,hR,hmeet⟩ := eighty_three_exists_anchor_meeting_le_fifty_five F hu hf hc
  let G := F.filter (fun S => S ∩ R = ∅)
  refine ⟨G,Finset.filter_subset _ _,?_,?_⟩
  · have hp := Finset.filter_card_add_filter_neg_card_eq_card
      (s := F) (p := fun S => (S ∩ R).Nonempty)
    simp only [Finset.not_nonempty_iff_eq_empty] at hp
    change (F.filter (fun S => (S ∩ R).Nonempty)).card + G.card = F.card at hp
    clear * - hp hc hmeet
    omega
  · intro S hS T hT
    exact disjoint_anchor_family_intersecting F R hR
      (Finset.card_pos.mp (by rw [hu R hR]; decide)) hf S hS T hT
      (Finset.card_pos.mp (by rw [hu S (Finset.mem_filter.mp hS).1]; decide))
      (Finset.card_pos.mp (by rw [hu T (Finset.mem_filter.mp hT).1]; decide))

/-- The conditional rank-four seed improves the refined rank-five consequence. -/
theorem rank_five_le_eight_hundred_twelve_of_intersecting_twenty_seven
    (hI : IntersectingRankFourUpper 27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 5) (hf : IsSunflowerFree F 3) : F.card ≤ 812 := by
  have hd : ∀ x, (F.filter (fun S => x ∈ S)).card ≤ 82 := by
    intro x
    have hb := unrestricted_upper_eighty_two_of_intersecting_twenty_seven hI
      (residualLink F {x})
      (by simpa using residualLink_uniform (core := {x}) hu)
      (residualLink_sunflowerFree hf)
    simpa [card_residualLink,upperStar] using hb
  have hb := card_le_refined_step F 5 3 82 (by decide) (by decide) hu hf hd
  exact hb

/-- One further refined incidence step at rank six, with the same explicit premise. -/
theorem rank_six_le_nine_thousand_seven_hundred_thirty_four_of_intersecting_twenty_seven
    (hI : IntersectingRankFourUpper 27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 6) (hf : IsSunflowerFree F 3) : F.card ≤ 9734 := by
  have hd : ∀ x, (F.filter (fun S => x ∈ S)).card ≤ 812 := by
    intro x
    have hb := rank_five_le_eight_hundred_twelve_of_intersecting_twenty_seven hI
      (residualLink F {x})
      (by simpa using residualLink_uniform (core := {x}) hu)
      (residualLink_sunflowerFree hf)
    simpa [card_residualLink,upperStar] using hb
  have hb := card_le_refined_step F 6 3 812 (by decide) (by decide) hu hf hd
  exact hb

end Erdos20V8Consequences
