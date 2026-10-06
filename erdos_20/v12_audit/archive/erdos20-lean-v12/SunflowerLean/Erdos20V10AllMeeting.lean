import SunflowerLean.Erdos20V10HighParityMain
import SunflowerLean.Erdos20V9ProfileBridge
import SunflowerLean.Erdos20V9Census

namespace Erdos20V10AllMeeting
open Erdos20BCWConditional Erdos20Incidence Erdos20V8Boundary Erdos20DegreeCongruences
open Erdos20V9ProfileBridge Erdos20V9Census Erdos20V9HighGraph
open Erdos20V9HighCompatibility Erdos20V10HighParity

/-- At minimum meeting size55, parity rules out the remaining degree17 case;
every supported point therefore has degree18,19 or20. -/
theorem all_meeting_at_least_fifty_five_degrees_eighteen_to_twenty
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (hm : ∀ R ∈ F, 55 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card) :
    ∀ x ∈ support F, 18 ≤ degree F x ∧ degree F x ≤ 20 := by
  intro x hx
  have hb := all_meeting_at_least_fifty_five_degrees F hu hf hm
    (member_high_points_card_le_two F hu hf) x hx
  refine ⟨?_,hb.2⟩
  by_contra hn
  have hd : degree F x = 17 := by omega
  have hxH : x ∉ highPoints F := by
    intro hh
    have := (Finset.mem_filter.mp hh).2
    omega
  apply low_high_transversal_degree_seventeen_impossible F hu hf x hxH hd
  intro R hR hxR
  have hp := meeting_at_least_fifty_five_member_structure F hu hf R hR (hm R hR)
  obtain ⟨y,hyR,hy20⟩ := (hp.2.2.1 x hxR hd).2
  exact ⟨y,Finset.mem_inter.mpr ⟨hyR,
    Finset.mem_filter.mpr ⟨member_subset_support hR hyR,hy20⟩⟩⟩

/-- The degree17 class vanishes under the same actual-family hypothesis. -/
theorem all_meeting_at_least_fifty_five_degree_seventeen_class_empty
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (hm : ∀ R ∈ F, 55 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card) :
    degreeClass F 17 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hxS,hx17⟩ := Finset.mem_filter.mp hx
  have hh := all_meeting_at_least_fifty_five_degrees_eighteen_to_twenty F hu hf hm x hxS
  omega

/-- Exact three-class census after excluding degree17. No I27 or fixed family
cardinality is assumed. -/
theorem all_meeting_at_least_fifty_five_degree_census
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (hm : ∀ R ∈ F, 55 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card) :
    18 * (degreeClass F 18).card + 19 * (degreeClass F 19).card +
      20 * (highPoints F).card = 4 * F.card ∧
    18 * (degreeClass F 18).card ≤ 2 * F.card ∧
    10 * (highPoints F).card ≤ 4 * ((degreeClass F 18).card + (degreeClass F 19).card) ∧
    (support F \ highPoints F).card = (degreeClass F 18).card + (degreeClass F 19).card := by
  have hb := all_meeting_at_least_fifty_five_degrees_eighteen_to_twenty F hu hf hm
  have hp : ∀ x ∈ support F, degree F x = 17 ∨ degree F x = 18 ∨
      degree F x = 19 ∨ degree F x = 20 := by
    intro x hx
    have := hb x hx
    omega
  have h17 : ∀ R ∈ F, (R.filter (fun x => degree F x = 17)).card ≤ 1 :=
    fun R hR => (meeting_at_least_fifty_five_low_degree_caps F hu hf R hR (hm R hR)).1
  have hsmall : ∀ R ∈ F, (R.filter (fun x => degree F x ≤ 18)).card ≤ 2 :=
    fun R hR => (meeting_at_least_fifty_five_low_degree_caps F hu hf R hR (hm R hR)).2
  obtain ⟨htotal,_,hsmallcount,hlow⟩ := rank_four_degree_census F hu hp h17 hsmall
  have hz : (degreeClass F 17).card = 0 := by
    rw [all_meeting_at_least_fifty_five_degree_seventeen_class_empty F hu hf hm]
    rfl
  simp only [hz,Nat.mul_zero,zero_add] at htotal hsmallcount hlow
  have hedge := ten_mul_high_card_le_four_mul_low_card F hu hf
    (member_high_points_card_le_two F hu hf)
  rw [hlow] at hedge
  exact ⟨htotal,hsmallcount,hedge,hlow⟩

/-- The three-class arithmetic at cardinality81 leaves four precise profiles,
rather than giving a contradiction by itself. -/
theorem eighty_one_three_class_census_profiles
    (b c d : ℕ) (ht : 18*b + 19*c + 20*d = 324)
    (hb : 18*b ≤ 162) (hedge : 10*d ≤ 4*(b+c)) :
    (b=0 ∧ c=16 ∧ d=1) ∨ (b=1 ∧ c=14 ∧ d=2) ∨
      (b=2 ∧ c=12 ∧ d=3) ∨ (b=3 ∧ c=10 ∧ d=4) := by
  omega

/-- Any actual81-member family with all meeting neighborhoods at least55 has
one of these four degree multiplicities. This is a necessary-condition result,
not an existence assertion for any numerical profile. -/
theorem eighty_one_all_meeting_degree_census
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3) (hc : F.card = 81)
    (hm : ∀ R ∈ F, 55 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card) :
    ((degreeClass F 18).card=0 ∧ (degreeClass F 19).card=16 ∧ (highPoints F).card=1) ∨
    ((degreeClass F 18).card=1 ∧ (degreeClass F 19).card=14 ∧ (highPoints F).card=2) ∨
    ((degreeClass F 18).card=2 ∧ (degreeClass F 19).card=12 ∧ (highPoints F).card=3) ∨
    ((degreeClass F 18).card=3 ∧ (degreeClass F 19).card=10 ∧ (highPoints F).card=4) := by
  obtain ⟨ht,hb,he,_⟩ := all_meeting_at_least_fifty_five_degree_census F hu hf hm
  apply eighty_one_three_class_census_profiles
    (degreeClass F 18).card (degreeClass F 19).card (highPoints F).card
  · simpa [hc] using ht
  · simpa [hc] using hb
  · exact he

/-- The same actual census excludes cardinalities87 and92 in the all-meeting55
class. This is a class restriction, not an unrestricted cardinality ceiling. -/
theorem no_eighty_seven_or_ninety_two_all_meeting_at_least_fifty_five
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (hc : F.card = 87 ∨ F.card = 92)
    (hm : ∀ R ∈ F, 55 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card) : False := by
  obtain ⟨ht,hb,he,_⟩ := all_meeting_at_least_fifty_five_degree_census F hu hf hm
  clear * - ht hb he hc
  omega

/-- Every surviving81-member near-boundary profile has exactly17 supported
points. It has between one and four degree-twenty points. -/
theorem eighty_one_all_meeting_support_seventeen
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3) (hc : F.card = 81)
    (hm : ∀ R ∈ F, 55 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card) :
    (support F).card = 17 ∧ 1 ≤ (highPoints F).card ∧ (highPoints F).card ≤ 4 := by
  have hp := eighty_one_all_meeting_degree_census F hu hf hc hm
  have hlow := (all_meeting_at_least_fifty_five_degree_census F hu hf hm).2.2.2
  have hs : highPoints F ⊆ support F := Finset.filter_subset _ _
  have ht := Finset.card_sdiff_add_card_inter (support F) (highPoints F)
  rw [Finset.inter_eq_right.mpr hs,hlow] at ht
  clear * - hp ht
  rcases hp with hp | hp | hp | hp <;> omega

end Erdos20V10AllMeeting
