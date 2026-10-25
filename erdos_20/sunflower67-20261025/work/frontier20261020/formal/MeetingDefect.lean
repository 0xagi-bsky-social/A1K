import SunflowerLean.Erdos20RankFour
import SunflowerLean.Erdos20DegreeCongruences

namespace FrontierMeetingDefect
open Erdos20BCWConditional Erdos20RankFour Erdos20RankThree Erdos20DegreeCongruences

/-- Keeping the actual anchor degrees instead of replacing each by twenty
gives a degree-sensitive bound on the meeting neighborhood. -/
theorem twice_meeting_add_two_le_degree_sum_add_forty
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3) :
    2 * (F.filter (fun S => (S ∩ R).Nonempty)).card + 2 ≤
      (∑ x ∈ R, degree F x) + 40 := by
  classical
  let N := F.filter (fun S => (S ∩ R).Nonempty)
  have hRN : R ∈ N := Finset.mem_filter.mpr ⟨hR,by
    rw [Finset.inter_self]
    exact Finset.card_pos.mp (by rw [hu R hR]; decide)⟩
  have huN : ∀ S ∈ N, S.card = 4 :=
    fun S hS => hu S (Finset.mem_filter.mp hS).1
  have hfN : IsSunflowerFree N 3 := fun H hH hsun =>
    hf H (hH.trans (Finset.filter_subset _ _)) hsun
  have hdef := meeting_incidence_singleton_defect N R hRN (hu R hR)
    (fun S hS => (Finset.mem_filter.mp hS).2)
  have hsingle := singleton_intersection_card_le_forty N R hRN huN hfN
  have hsum : (∑ x ∈ R, (N.filter (fun S => x ∈ S)).card) ≤
      ∑ x ∈ R, degree F x := by
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.card_le_card
    intro S hS
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1,
        (Finset.mem_filter.mp hS).2⟩
  change 2 * N.card + 2 ≤ _
  omega

/-- A degree-sum budget yields a lower bound on the number of disjoint
members. All arithmetic is in naturals; no truncated subtraction is needed. -/
theorem twice_card_le_twice_disjoint_add_degree_sum_add_thirty_eight
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3) :
    2 * F.card ≤
      2 * (F.filter (fun S => S ∩ R = ∅)).card + (∑ x ∈ R, degree F x) + 38 := by
  have h := twice_meeting_add_two_le_degree_sum_add_forty F R hR hu hf
  have hp := Finset.filter_card_add_filter_neg_card_eq_card
    (s := F) (p := fun S => (S ∩ R).Nonempty)
  simp only [Finset.not_nonempty_iff_eq_empty] at hp
  omega

/-- The numerical form needed for a sixty-one-member residual family and
an anchor whose four point degrees sum to at most sixty-six. -/
theorem sixty_one_degree_sum_sixty_six_has_nine_disjoint
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hc : F.card = 61) (hd : (∑ x ∈ R, degree F x) ≤ 66) :
    9 ≤ (F.filter (fun S => S ∩ R = ∅)).card := by
  have h := twice_card_le_twice_disjoint_add_degree_sum_add_thirty_eight F R hR hu hf
  omega

end FrontierMeetingDefect
