import SunflowerLean.Erdos20V10FiniteEndgame
import SunflowerLean.Erdos20V10HighTriangleIncidence

namespace Erdos20V11Census
open Erdos20BCWConditional Erdos20DegreeCongruences Erdos20ExtremalSupport
open Erdos20V8Targets Erdos20V9Census Erdos20V8Boundary Erdos20V10BoundaryReduction
open Erdos20V10Profile54Seventeen Erdos20V10FiniteEndgame

/-- Exact degree and support sums for the four possible degrees, with no
local incidence-cap assumption. -/
theorem four_degree_census_identity
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4)
    (hp : ∀ x ∈ support F, 17 ≤ degree F x ∧ degree F x ≤ 20) :
    17*(degreeClass F 17).card + 18*(degreeClass F 18).card +
      19*(degreeClass F 19).card + 20*(highPoints F).card = 4*F.card ∧
    (degreeClass F 17).card + (degreeClass F 18).card +
      (degreeClass F 19).card + (highPoints F).card = (support F).card := by
  classical
  have hd (x) (hx : x ∈ support F) : degree F x=17 ∨ degree F x=18 ∨
      degree F x=19 ∨ degree F x=20 := by have := hp x hx; omega
  constructor
  · calc
      _ = ∑ x ∈ support F, degree F x := by
        simp only [degreeClass,highPoints,Finset.card_filter,Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        rcases hd x hx with h | h | h | h <;> simp [h]
      _ = _ := by simpa [Nat.mul_comm] using support_degree_sum F 4 hu
  · rw [Finset.card_eq_sum_ones (s := support F)]
    simp only [degreeClass,highPoints,Finset.card_filter,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rcases hd x hx with h | h | h | h <;> simp [h]

/-- All exact census constraints obtained for an81-member family under I27.
The intersecting ceiling remains an explicit ordinary hypothesis. -/
theorem conditional_eighty_one_census
    (hI : IntersectingRankFourUpper 27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3) (hc : F.card=81) :
    let a := (degreeClass F 17).card
    let b := (degreeClass F 18).card
    let c := (degreeClass F 19).card
    let d := (highPoints F).card
    (a+b+c+d=17 ∨ a+b+c+d=18) ∧ a≤4 ∧
    17*a+18*b+19*c+20*d=324 ∧ 11*d≤4*(a+b+c) ∧ 1≤c+d := by
  classical
  dsimp only
  obtain ⟨hlo,_,_⟩ := conditional_eighty_one_min_degree_and_support hI F hu hf hc
  have hp : ∀ x ∈ support F, 17 ≤ degree F x ∧ degree F x ≤ 20 := by
    intro x hx
    exact ⟨hlo x hx,Erdos20RankFour.rank_four_degree_le_twenty F hu hf x⟩
  obtain ⟨ht,hs⟩ := four_degree_census_identity F hu hp
  have hsupport := conditional_eighty_one_support_seventeen_or_eighteen hI F hu hf hc
  have hm : ∀ R ∈ F, 54 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card := by
    intro R hR
    have := meeting_lower_bound_of_intersecting_upper hI F hu hf R hR
    omega
  have hcap := degree_seventeen_member_card_le_one F hu hf hm
  have ha := degree_predicate_incidence_le F (fun d => d=17) 1 hcap
  change (∑ x ∈ degreeClass F 17, degree F x) ≤ 1*F.card at ha
  rw [degreeClass_sum] at ha
  have hedge := Erdos20V10HighTriangle.eleven_mul_high_card_le_four_mul_low_card F hu hf
  have hlow := Finset.card_sdiff_add_card_inter (support F) (highPoints F)
  have hsub : highPoints F ⊆ support F := Finset.filter_subset _ _
  rw [Finset.inter_eq_right.mpr hsub] at hlow
  have hex := conditional_eighty_one_has_degree_nineteen_or_twenty hI F hu hf hc
  have hcd : 1 ≤ (degreeClass F 19).card + (highPoints F).card := by
    obtain ⟨x,hx,hx19 | hx20⟩ := hex
    · have : 0 < (degreeClass F 19).card := Finset.card_pos.mpr
        ⟨x,Finset.mem_filter.mpr ⟨hx,hx19⟩⟩
      omega
    · have : 0 < (highPoints F).card := Finset.card_pos.mpr
        ⟨x,Finset.mem_filter.mpr ⟨hx,hx20⟩⟩
      omega
  clear * - hc hs hsupport ht ha hedge hlow hcd
  omega

/-- Compact arithmetic description of the six support17 and eight support18
possibilities. These are necessary profiles, not existence certificates. -/
theorem fourteen_census_profiles_arithmetic
    (a b c d : ℕ) (hs : a+b+c+d=17 ∨ a+b+c+d=18) (ha : a≤4)
    (ht : 17*a+18*b+19*c+20*d=324) (he : 11*d≤4*(a+b+c)) (hp : 1≤c+d) :
    (a+b+c+d=17 ∧ ((a=0 ∧ 1≤d ∧ d≤4 ∧ b+1=d ∧ c+2*d=18) ∨
      (a=1 ∧ 3≤d ∧ d≤4 ∧ b+3=d ∧ c+2*d=19))) ∨
    (a+b+c+d=18 ∧ a=c+2*d ∧ 1≤c+d ∧ c+2*d≤4) := by
  omega

/-- Actual conditional81-member families lie in the compact fourteen-profile
census. No external enumeration or finite-search certificate is used. -/
theorem conditional_eighty_one_fourteen_profiles
    (hI : IntersectingRankFourUpper 27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3) (hc : F.card=81) :
    let a := (degreeClass F 17).card
    let b := (degreeClass F 18).card
    let c := (degreeClass F 19).card
    let d := (highPoints F).card
    (a+b+c+d=17 ∧ ((a=0 ∧ 1≤d ∧ d≤4 ∧ b+1=d ∧ c+2*d=18) ∨
      (a=1 ∧ 3≤d ∧ d≤4 ∧ b+3=d ∧ c+2*d=19))) ∨
    (a+b+c+d=18 ∧ a=c+2*d ∧ 1≤c+d ∧ c+2*d≤4) := by
  obtain ⟨hs,ha,ht,he,hp⟩ := conditional_eighty_one_census hI F hu hf hc
  exact fourteen_census_profiles_arithmetic _ _ _ _ hs ha ht he hp

end Erdos20V11Census
