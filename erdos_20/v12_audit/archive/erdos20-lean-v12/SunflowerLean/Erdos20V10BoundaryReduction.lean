import SunflowerLean.Erdos20V10MinimumDegree
import SunflowerLean.Erdos20V9Final
import SunflowerLean.Erdos20V10Profile54DegreeCap

namespace Erdos20V10BoundaryReduction
open Erdos20BCWConditional Erdos20RankThree Erdos20V8Targets
open Erdos20DegreeCongruences Erdos20ExtremalSupport Erdos20V10MinimumDegree

/-- The explicit intersecting ceiling bounds the number of members disjoint
from each anchor. No external search result is imported as an axiom. -/
theorem meeting_lower_bound_of_intersecting_upper
    (hI : IntersectingRankFourUpper 27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (R : Finset α) (hR : R ∈ F) :
    F.card ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card + 27 := by
  classical
  let D := F.filter (fun S => S ∩ R = ∅)
  have hDu : ∀ S ∈ D, S.card=4 := fun S hS => hu S (Finset.mem_filter.mp hS).1
  have hDf : IsSunflowerFree D 3 := fun H hH hs => hf H
    (hH.trans (Finset.filter_subset _ _)) hs
  have hDi : ∀ S ∈ D, ∀ T ∈ D, (S ∩ T).Nonempty := by
    intro S hS T hT
    exact disjoint_anchor_family_intersecting F R hR
      (Finset.card_pos.mp (by rw [hu R hR]; decide)) hf S hS T hT
      (Finset.card_pos.mp (by rw [hDu S hS]; decide))
      (Finset.card_pos.mp (by rw [hDu T hT]; decide))
  have hd := hI D hDu hDf hDi
  have hp := Finset.filter_card_add_filter_neg_card_eq_card (s := F)
    (p := fun S => (S ∩ R).Nonempty)
  simp only [Finset.not_nonempty_iff_eq_empty] at hp
  change (F.filter (fun S => (S ∩ R).Nonempty)).card + D.card = F.card at hp
  omega

/-- Any81-member counterexample to a conditional80 bound has all point degrees
at least17, and its support has between17 and19 points. -/
theorem conditional_eighty_one_min_degree_and_support
    (hI : IntersectingRankFourUpper 27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3) (hc : F.card=81) :
    (∀ x ∈ support F, 17 ≤ degree F x) ∧
    17 ≤ (support F).card ∧ (support F).card ≤ 19 := by
  classical
  have hm : ∀ R ∈ F, 54 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card := by
    intro R hR
    have hh := meeting_lower_bound_of_intersecting_upper hI F hu hf R hR
    omega
  have hd := all_meeting_fifty_four_min_degree_seventeen F hu hf hm
  refine ⟨hd,?_,?_⟩
  all_goals
    have hsum : (∑ x ∈ support F, degree F x) = 4 * F.card := by
      simpa [Nat.mul_comm] using support_degree_sum F 4 hu
    have hlo : 17 * (support F).card ≤ ∑ x ∈ support F, degree F x := by
      calc
        _ = ∑ _x ∈ support F, 17 := by simp [Nat.mul_comm]
        _ ≤ _ := Finset.sum_le_sum hd
    have hhi : (∑ x ∈ support F, degree F x) ≤ 20 * (support F).card := by
      calc
        _ ≤ ∑ _x ∈ support F, 20 := Finset.sum_le_sum (fun x _ =>
          Erdos20RankFour.rank_four_degree_le_twenty F hu hf x)
        _ = _ := by simp [Nat.mul_comm]
    omega

/-- The remaining81-member case must contain a supported point of degree19 or20.
The degree-at-most18 class has been completely excluded under the explicit I27. -/
theorem conditional_eighty_one_has_degree_nineteen_or_twenty
    (hI : IntersectingRankFourUpper 27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3) (hc : F.card=81) :
    ∃ x ∈ support F, degree F x=19 ∨ degree F x=20 := by
  classical
  have hex : ∃ x, 19 ≤ degree F x := by
    by_contra hn
    push_neg at hn
    have hb := Erdos20V10Profile54DegreeCap.card_le_eighty_of_degree_cap_eighteen
      hI F hu hf (fun x => by have := hn x; omega)
    omega
  obtain ⟨x,hx⟩ := hex
  have hpos : 0 < (F.filter (fun R => x ∈ R)).card := by change 0 < degree F x; omega
  obtain ⟨R,hR⟩ := Finset.card_pos.mp hpos
  obtain ⟨hRF,hxR⟩ := Finset.mem_filter.mp hR
  refine ⟨x,member_subset_support hRF hxR,?_⟩
  have hh := Erdos20RankFour.rank_four_degree_le_twenty F hu hf x
  change degree F x ≤ 20 at hh
  omega

end Erdos20V10BoundaryReduction
