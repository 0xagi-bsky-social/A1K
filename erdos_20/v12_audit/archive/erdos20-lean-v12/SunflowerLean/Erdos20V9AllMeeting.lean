import SunflowerLean.Erdos20V9HighCompatibilityMain
import SunflowerLean.Erdos20V9WeightCongruence

namespace Erdos20V9AllMeeting
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20V8Boundary Erdos20DegreeCongruences Erdos20MeetingFiftySix
open Erdos20V9HighCompatibility Erdos20V9WeightCongruence

/-- Every degree-twenty point has reciprocal incidence weight divisible by fifteen. -/
theorem high_point_weight_mod_fifteen_unconditional
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) :
    pointWeight F (highPoints F) x % 15 = 0 :=
  high_point_weight_mod_fifteen F hu hf (member_high_points_card_le_two F hu hf) x hx

/-- A degree-twenty transversal forces cardinality divisible by five;
the at-most-two condition is supplied by the structural theorem. -/
theorem card_mod_five_of_high_transversal_unconditional
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (hhit : ∀ R ∈ F, (R ∩ highPoints F).Nonempty) : F.card % 5 = 0 :=
  card_mod_five_of_high_transversal F hu hf (fun R hR =>
    ⟨Finset.card_pos.mpr (hhit R hR),member_high_points_card_le_two F hu hf R hR⟩)

/-- A nonzero residue modulo five exposes a member containing no degree-twenty point. -/
theorem exists_member_avoiding_high_of_card_not_mod_five
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (hmod : F.card % 5 ≠ 0) : ∃ R ∈ F, R ∩ highPoints F = ∅ := by
  by_contra hn
  push_neg at hn
  apply hmod
  apply card_mod_five_of_high_transversal_unconditional F hu hf
  intro R hR
  exact hn R hR

/-- No nonempty rank-four three-sunflower-free family has all meeting neighborhoods
of size fifty-six. This removes the cardinality83 restriction of the earlier result. -/
theorem no_all_meeting_fifty_six
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3) (hne : F.Nonempty)
    (hm : ∀ R ∈ F, (F.filter (fun S => (S ∩ R).Nonempty)).card = 56) : False :=
  no_all_meeting_fifty_six_of_high_cap F hu hf hne
    (member_high_points_card_le_two F hu hf) hm

/-- Every nonempty rank-four three-sunflower-free family has an anchor meeting
at most fifty-five members. Other anchors may still have meeting size fifty-six. -/
theorem exists_anchor_meeting_le_fifty_five
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3) (hne : F.Nonempty) :
    ∃ R ∈ F, (F.filter (fun S => (S ∩ R).Nonempty)).card ≤ 55 := by
  classical
  by_contra hn
  push_neg at hn
  apply no_all_meeting_fifty_six F hu hf hne
  intro R hR
  have hlo := hn R hR
  have hhi := meeting_neighborhood_card_le_fifty_six F R hR hu hf
  omega

end Erdos20V9AllMeeting
