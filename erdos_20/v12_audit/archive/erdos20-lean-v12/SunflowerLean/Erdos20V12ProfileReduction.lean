import SunflowerLean.Erdos20V12DegreeSeventeen

namespace Erdos20V12Profile
open Erdos20BCWConditional Erdos20DegreeCongruences Erdos20V8Targets
open Erdos20V9Census Erdos20V8Boundary Erdos20V11Census Erdos20V12DegreeSeventeen

/-- The two degree profiles left after the actual degree-seventeen class
has been eliminated. Neither profile is asserted to be realizable. -/
def TwoCensusProfiles (b c d : ℕ) : Prop :=
    (b=0 ∧ c=16 ∧ d=1) ∨ (b=1 ∧ c=14 ∧ d=2)

/-- An81-member family under I27 has no supported degree-seventeen points. -/
theorem conditional_eighty_one_degree_class_seventeen_empty
    (hI : IntersectingRankFourUpper 27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3) (hc : F.card=81) :
    degreeClass F 17=∅ := by
  have hm : ∀ R ∈ F, 54 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card := by
    intro R hR
    have hh := Erdos20V10BoundaryReduction.meeting_lower_bound_of_intersecting_upper hI F hu hf R hR
    omega
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact all_meeting_fifty_four_degree_ne_seventeen F hu hf hm x (Finset.mem_filter.mp hx).2

/-- The ten inherited actual-family profiles reduce to two, both on
seventeen supported points, with all degrees between eighteen and twenty. -/
theorem conditional_eighty_one_two_profiles
    (hI : IntersectingRankFourUpper 27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3) (hc : F.card=81) :
    (support F).card=17 ∧ degreeClass F 17=∅ ∧
    TwoCensusProfiles (degreeClass F 18).card (degreeClass F 19).card (highPoints F).card := by
  have he := conditional_eighty_one_degree_class_seventeen_empty hI F hu hf hc
  have hp := conditional_eighty_one_ten_profiles hI F hu hf hc
  have hprof : TwoCensusProfiles (degreeClass F 18).card
      (degreeClass F 19).card (highPoints F).card := by
    simpa [TenCensusProfiles,TwoCensusProfiles,he] using hp
  obtain ⟨hs,ha,ht,hedge,hpos⟩ := conditional_eighty_one_census hI F hu hf hc
  have hs17 : (support F).card=17 := by
    have hdeg : ∀ x ∈ support F, 17 ≤ degree F x ∧ degree F x ≤ 20 := by
      intro x hx
      exact ⟨(Erdos20V10BoundaryReduction.conditional_eighty_one_min_degree_and_support hI F hu hf hc).1 x hx,
        Erdos20RankFour.rank_four_degree_le_twenty F hu hf x⟩
    have hsum := (four_degree_census_identity F hu hdeg).2
    rw [he,Finset.card_empty] at hsum
    rcases hprof with h | h <;> obtain ⟨hb,hc,hd⟩ := h <;> omega
  exact ⟨hs17,he,hprof⟩

/-- I27 together with an80 ceiling for the two explicitly retained boundary
profiles suffices for the unrestricted80 ceiling. The restricted ceiling is
an ordinary, still-unproved mathematical argument. -/
theorem unrestricted_eighty_of_two_boundary_profiles
    (hI : IntersectingRankFourUpper 27)
    (hboundary : ∀ {α : Type} [DecidableEq α] (F : Finset (Finset α)),
      (∀ R ∈ F, R.card=4) → IsSunflowerFree F 3 → (support F).card=17 →
      degreeClass F 17=∅ →
      TwoCensusProfiles (degreeClass F 18).card (degreeClass F 19).card (highPoints F).card →
      (∀ R ∈ F, (R ∩ highPoints F).card≤1) → F.card≤80) : RankFourUpper 80 := by
  intro α inst F hu hf
  have h81 := Erdos20V9Final.unrestricted_upper_eighty_one_of_intersecting_twenty_seven hI F hu hf
  by_contra hn
  have hc : F.card=81 := by omega
  obtain ⟨hs,h17,hprof⟩ := conditional_eighty_one_two_profiles hI F hu hf hc
  have hcap := (Erdos20V11Final.conditional_eighty_one_boundary_rigidity hI F hu hf hc).2.2.2
  have h80 := hboundary F hu hf hs h17 hprof hcap
  omega

end Erdos20V12Profile
