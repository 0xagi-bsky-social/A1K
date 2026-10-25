import SunflowerLean.Erdos20V8Targets

namespace Erdos20V8BoundaryReduction
open Erdos20V8Targets Erdos20RankThree Erdos20MeetingFiftySix

/-- At cardinality83, the external intersecting ceiling27 and the proved
meeting ceiling56 force equality at every anchor. -/
theorem eighty_three_all_meeting_fifty_six
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hc : F.card = 83) (hI : IntersectingRankFourUpper 27)
    (R : Finset α) (hR : R ∈ F) :
    (F.filter (fun S => (S ∩ R).Nonempty)).card = 56 := by
  classical
  let D := F.filter (fun S => S ∩ R = ∅)
  have hdu : ∀ S ∈ D, S.card = 4 := fun S hS => hu S (Finset.mem_filter.mp hS).1
  have hdf : IsSunflowerFree D 3 := by
    intro G hG hsun
    exact hf G (hG.trans (Finset.filter_subset _ _)) hsun
  have hdi : ∀ S ∈ D, ∀ T ∈ D, (S ∩ T).Nonempty := by
    intro S hS T hT
    exact disjoint_anchor_family_intersecting F R hR
      (Finset.card_pos.mp (by rw [hu R hR]; decide)) hf S hS T hT
      (Finset.card_pos.mp (by rw [hdu S hS]; decide))
      (Finset.card_pos.mp (by rw [hdu T hT]; decide))
  have hd := hI D hdu hdf hdi
  have hm := meeting_neighborhood_card_le_fifty_six F R hR hu hf
  have hp := Finset.filter_card_add_filter_neg_card_eq_card
    (s := F) (p := fun S => (S ∩ R).Nonempty)
  simp only [Finset.not_nonempty_iff_eq_empty] at hp
  change (F.filter (fun S => (S ∩ R).Nonempty)).card + D.card = F.card at hp
  clear * - hd hm hp hc
  omega

/-- An exact interface for the boundary proof. Both inputs are explicit:
the intersecting ceiling27 and exclusion of the all-meeting56 boundary. -/
theorem unrestricted_eighty_two_of_boundary_exclusion
    (hI : IntersectingRankFourUpper 27)
    (hboundary : ∀ {α : Type} [DecidableEq α] (F : Finset (Finset α)),
      (∀ S ∈ F, S.card = 4) → IsSunflowerFree F 3 → F.card = 83 →
      (∀ R ∈ F, (F.filter (fun S => (S ∩ R).Nonempty)).card = 56) → False) :
    RankFourUpper 82 := by
  intro α inst F hu hf
  have hb := unrestricted_upper_eighty_three_of_intersecting_twenty_seven hI F hu hf
  by_contra hn
  have hc : F.card = 83 := by omega
  exact hboundary F hu hf hc (eighty_three_all_meeting_fifty_six F hu hf hc hI)

end Erdos20V8BoundaryReduction
