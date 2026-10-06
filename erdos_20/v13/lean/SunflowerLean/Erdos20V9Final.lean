import SunflowerLean.Erdos20V9ProfileBridge
import SunflowerLean.Erdos20V9BoundaryArithmetic
import SunflowerLean.Erdos20V9Census
import SunflowerLean.Erdos20V9HighCompatibilityMain
import SunflowerLean.Erdos20V9HighGraph
import SunflowerLean.Erdos20V8Final

namespace Erdos20V9Final
open Erdos20BCWConditional Erdos20RankThree Erdos20V8Boundary Erdos20DegreeCongruences
open Erdos20V9ProfileBridge Erdos20V9BoundaryArithmetic Erdos20V9Census
open Erdos20V9HighGraph Erdos20V9HighCompatibility Erdos20V8Targets

/-- An actual82-member family cannot have every meeting neighborhood at least55.
No intersecting upper bound is assumed. -/
theorem no_eighty_two_all_meeting_at_least_fifty_five
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3) (hc : F.card=82)
    (hm : ∀ R ∈ F, 55 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card) : False := by
  have hcap := member_high_points_card_le_two F hu hf
  have hd := all_meeting_at_least_fifty_five_degrees F hu hf hm hcap
  have hp : ∀ x ∈ support F, degree F x=17 ∨ degree F x=18 ∨ degree F x=19 ∨ degree F x=20 := by
    intro x hx
    have := hd x hx
    omega
  have h17 : ∀ R ∈ F, (R.filter (fun x => degree F x=17)).card ≤ 1 :=
    fun R hR => (meeting_at_least_fifty_five_low_degree_caps F hu hf R hR (hm R hR)).1
  have hsmall : ∀ R ∈ F, (R.filter (fun x => degree F x≤18)).card ≤ 2 :=
    fun R hR => (meeting_at_least_fifty_five_low_degree_caps F hu hf R hR (hm R hR)).2
  obtain ⟨htotal,ha,hab,hlow⟩ := rank_four_degree_census F hu hp h17 hsmall
  have hedge := ten_mul_high_card_le_four_mul_low_card F hu hf hcap
  rw [hlow] at hedge
  apply no_eighty_two_degree_census (degreeClass F 17).card (degreeClass F 18).card
    (degreeClass F 19).card (highPoints F).card
  · simpa [hc] using htotal
  · simpa [hc] using ha
  · simpa [hc] using hab
  · exact hedge

/-- A hypothetical82-member family has an anchor meeting at most54 members. -/
theorem eighty_two_exists_anchor_meeting_le_fifty_four
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3) (hc : F.card=82) :
    ∃ R ∈ F, (F.filter (fun S => (S ∩ R).Nonempty)).card ≤ 54 := by
  classical
  by_contra hn
  push_neg at hn
  exact no_eighty_two_all_meeting_at_least_fifty_five F hu hf hc (fun R hR => by have := hn R hR; omega)

/-- A hypothetical82-member family contains an intersecting subfamily of at least28.
The statement is unconditional under its literal rank/cardinality/SF3 hypotheses. -/
theorem eighty_two_contains_intersecting_twenty_eight
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3) (hc : F.card=82) :
    ∃ G ⊆ F, 28 ≤ G.card ∧ (∀ S ∈ G, ∀ T ∈ G, (S ∩ T).Nonempty) := by
  classical
  obtain ⟨R,hR,hmeet⟩ := eighty_two_exists_anchor_meeting_le_fifty_four F hu hf hc
  let G := F.filter (fun S => S ∩ R=∅)
  refine ⟨G,Finset.filter_subset _ _,?_,?_⟩
  · have hp := Finset.filter_card_add_filter_neg_card_eq_card (s := F) (p := fun S => (S ∩ R).Nonempty)
    simp only [Finset.not_nonempty_iff_eq_empty] at hp
    change (F.filter (fun S => (S ∩ R).Nonempty)).card+G.card=F.card at hp
    omega
  · intro S hS T hT
    exact disjoint_anchor_family_intersecting F R hR
      (Finset.card_pos.mp (by rw [hu R hR]; decide)) hf S hS T hT
      (Finset.card_pos.mp (by rw [hu S (Finset.mem_filter.mp hS).1]; decide))
      (Finset.card_pos.mp (by rw [hu T (Finset.mem_filter.mp hT).1]; decide))

/-- A formal conditional upper81. The intersecting upper27 premise remains explicit. -/
theorem unrestricted_upper_eighty_one_of_intersecting_twenty_seven
    (hI : IntersectingRankFourUpper 27) : RankFourUpper 81 := by
  intro α inst F hu hf
  have hb := Erdos20V8Final.unrestricted_upper_eighty_two_of_intersecting_twenty_seven hI F hu hf
  by_contra hn
  have hc : F.card=82 := by omega
  obtain ⟨G,hGF,h28,hGi⟩ := eighty_two_contains_intersecting_twenty_eight F hu hf hc
  have h27 := hI G (fun S hS => hu S (hGF hS))
    (fun H hH hs => hf H (hH.trans hGF) hs) hGi
  omega

end Erdos20V9Final
