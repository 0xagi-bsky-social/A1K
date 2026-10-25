import SunflowerLean.Erdos20V11CensusIndependentTriple
import SunflowerLean.Erdos20V11CensusTenProfiles
import SunflowerLean.Erdos20V11EdgeThird

namespace Erdos20V11Census
open Erdos20BCWConditional Erdos20DegreeCongruences Erdos20ExtremalSupport
open Erdos20V8Boundary Erdos20V9HighGraph Erdos20V9Census Erdos20V8Targets
open Erdos20V10BoundaryReduction Erdos20V10FiniteEndgame Erdos20V11EdgeThird

/-- A hypothetical81-member family under I27 has at most two degree-twenty
points: every high triple either contains a high edge or is independent,
and both possibilities have been excluded by actual-family arguments. -/
theorem conditional_eighty_one_high_card_le_two
    (hI : IntersectingRankFourUpper 27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R∈F, R.card=4) (hf : IsSunflowerFree F 3) (hc : F.card=81) :
    (highPoints F).card≤2 := by
  classical
  by_contra hn
  have hh : 2 < (highPoints F).card := by omega
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ := Finset.two_lt_card_iff.mp hh
  have hs := (conditional_eighty_one_min_degree_and_support hI F hu hf hc).2.2
  by_cases hyNx : y∈highNeighbors F x
  · have := high_edge_third_high_support_ge_twenty F hu hf x hx y hyNx z hz hxz hyz
    omega
  by_cases hzNx : z∈highNeighbors F x
  · have := high_edge_third_high_support_ge_twenty F hu hf x hx z hzNx y hy hxy (Ne.symm hyz)
    omega
  by_cases hzNy : z∈highNeighbors F y
  · have := high_edge_third_high_support_ge_twenty F hu hf y hy z hzNy x hx (Ne.symm hxy) (Ne.symm hxz)
    omega
  exact conditional_eighty_one_no_independent_high_triple hI F hu hf hc
    x y z hx hy hz hxy hxz hyz hyNx hzNx hzNy

/-- The unconditional-in-geometry ten-profile classification of the conditional
81-member boundary. Only I27 remains an external mathematical premise. -/
theorem conditional_eighty_one_ten_profiles
    (hI : IntersectingRankFourUpper 27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R∈F, R.card=4) (hf : IsSunflowerFree F 3) (hc : F.card=81) :
    TenCensusProfiles (degreeClass F 17).card (degreeClass F 18).card
      (degreeClass F 19).card (highPoints F).card :=
  conditional_eighty_one_ten_profiles_of_high_card_le_two hI F hu hf hc
    (conditional_eighty_one_high_card_le_two hI F hu hf hc)

/-- Consolidated boundary structure, with no numerical profile asserted to be
realizable and no finite-search exclusion assumed. -/
theorem conditional_eighty_one_boundary_structure
    (hI : IntersectingRankFourUpper 27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R∈F, R.card=4) (hf : IsSunflowerFree F 3) (hc : F.card=81) :
    ((support F).card=17 ∨ (support F).card=18) ∧ (highPoints F).card≤2 ∧
    TenCensusProfiles (degreeClass F 17).card (degreeClass F 18).card
      (degreeClass F 19).card (highPoints F).card :=
  ⟨conditional_eighty_one_support_seventeen_or_eighteen hI F hu hf hc,
    conditional_eighty_one_high_card_le_two hI F hu hf hc,
    conditional_eighty_one_ten_profiles hI F hu hf hc⟩

/-- Sharper finite-support endgame: I27 plus an80 ceiling on at most18 supported
points with at most two high points suffices for the unrestricted80 ceiling.
Both still-unresolved hypotheses remain ordinary arguments. -/
theorem unrestricted_eighty_of_small_support_two_high_eighty
    (hI : IntersectingRankFourUpper 27)
    (hsmall : ∀ {α : Type} [DecidableEq α] (F : Finset (Finset α)),
      (∀ R∈F, R.card=4) → IsSunflowerFree F 3 → (support F).card≤18 →
      (highPoints F).card≤2 → F.card≤80) : RankFourUpper 80 := by
  intro α inst F hu hf
  have h81 := Erdos20V9Final.unrestricted_upper_eighty_one_of_intersecting_twenty_seven hI F hu hf
  by_contra hn
  have hc : F.card=81 := by omega
  obtain ⟨hs,hd,_⟩ := conditional_eighty_one_boundary_structure hI F hu hf hc
  have h80 := hsmall F hu hf (by omega) hd
  omega

end Erdos20V11Census
