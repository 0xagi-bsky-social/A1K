import SunflowerLean.Erdos20V11HighEdgeDegree
import SunflowerLean.Erdos20V11CensusFinal
import SunflowerLean.Erdos20V11DegreeSeventeenTrace

namespace Erdos20V11Final
open Erdos20BCWConditional Erdos20DegreeCongruences Erdos20V8Boundary
open Erdos20V9HighGraph Erdos20V8Targets Erdos20V11Census
open Erdos20V11HighEdgeDegree Erdos20V10BoundaryReduction

/-- High-point adjacency is empty whenever every supported degree is at least
fifteen. The actual edge-residual degree obstruction is discharged. -/
theorem high_neighbors_empty_of_min_degree_fifteen
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (hmin : ∀ u ∈ support F, 15 ≤ degree F u) :
    ∀ x ∈ highPoints F, highNeighbors F x=∅ := by
  intro x hx
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  exact no_high_edge_of_min_degree_fifteen F hu hf hmin x hx y hy

/-- The all-meeting54 regime has no member containing two high points. -/
theorem all_meeting_fifty_four_member_high_cap_one
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (hm : ∀ R ∈ F, 54 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card) :
    ∀ R ∈ F, (R ∩ highPoints F).card≤1 := by
  apply member_high_cap_one_of_high_neighbors_empty F
  apply high_neighbors_empty_of_min_degree_fifteen F hu hf
  intro u huS
  have := Erdos20V10MinimumDegree.all_meeting_fifty_four_min_degree_seventeen F hu hf hm u huS
  omega

/-- Consolidated literal-family81 boundary: at most two independent high
points, support17 or18, and one of ten exact necessary degree profiles. -/
theorem conditional_eighty_one_boundary_rigidity
    (hI : IntersectingRankFourUpper 27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3) (hc : F.card=81) :
    ((support F).card=17 ∨ (support F).card=18) ∧ (highPoints F).card≤2 ∧
    TenCensusProfiles (Erdos20V9Census.degreeClass F 17).card
      (Erdos20V9Census.degreeClass F 18).card (Erdos20V9Census.degreeClass F 19).card
      (highPoints F).card ∧ (∀ R ∈ F, (R ∩ highPoints F).card≤1) := by
  obtain ⟨hs,hd,hp⟩ := conditional_eighty_one_boundary_structure hI F hu hf hc
  refine ⟨hs,hd,hp,?_⟩
  apply member_high_cap_one_of_high_neighbors_empty F
  apply high_neighbors_empty_of_min_degree_fifteen F hu hf
  intro u huS
  have := (conditional_eighty_one_min_degree_and_support hI F hu hf hc).1 u huS
  omega

/-- The remaining80 endgame can be restricted further to families with
at most two high points and no member containing both. I27 and the restricted
80 ceiling remain explicit unproved mathematical arguments. -/
theorem unrestricted_eighty_of_small_support_independent_two_high_eighty
    (hI : IntersectingRankFourUpper 27)
    (hsmall : ∀ {α : Type} [DecidableEq α] (F : Finset (Finset α)),
      (∀ R ∈ F, R.card=4) → IsSunflowerFree F 3 → (support F).card≤18 →
      (highPoints F).card≤2 → (∀ R ∈ F, (R ∩ highPoints F).card≤1) → F.card≤80) :
    RankFourUpper 80 := by
  intro α inst F hu hf
  have h81 := Erdos20V9Final.unrestricted_upper_eighty_one_of_intersecting_twenty_seven hI F hu hf
  by_contra hn
  have hc : F.card=81 := by omega
  obtain ⟨hs,hd,_,hcap⟩ := conditional_eighty_one_boundary_rigidity hI F hu hf hc
  have := hsmall F hu hf (by omega) hd hcap
  omega

end Erdos20V11Final
