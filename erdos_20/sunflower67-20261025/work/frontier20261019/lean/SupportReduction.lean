import SupportFinish56
import SupportFinish53

namespace FrontierSupportReduction
open Erdos20BCWConditional Erdos20DegreeCongruences
open Erdos20V8Targets Erdos20V13FiniteReduction
open FrontierSupport FrontierSupportFinish

universe u

/-- Every intersecting counterexample, in an arbitrary universe, has a 28-member
injective relabelling on 56 points. This statement does not exclude that obstruction. -/
theorem finite56_obstruction_of_counterexample
    {α : Type u} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : 27 < F.card) :
    FiniteIntersectingObstructionOn 56 := by
  obtain ⟨H, hsub, hcard⟩ := Finset.exists_subset_card_eq (show 28 ≤ F.card by omega)
  have hHu : ∀ S ∈ H, S.card = 4 := fun S hS => hu S (hsub hS)
  have hHf : IsSunflowerFree H 3 := fun G hG => hf G (hG.trans hsub)
  have hHi : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty :=
    fun S hS T hT => hi S (hsub hS) T (hsub hT)
  have hs := intersecting_twenty_eight_support_le_fifty_six H hHu hHf hHi hcard
  obtain ⟨G, hGc, hGu, hGf, hGi⟩ :=
    exists_intersecting_fin_relabel H 56 4 3 hs hHu hHf hHi
  exact ⟨G, hGc.trans hcard, hGu, hGf, hGi⟩

/-- The stronger 53-point finite reduction, valid for counterexamples in any universe. -/
theorem finite53_obstruction_of_counterexample
    {α : Type u} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : 27 < F.card) :
    FiniteIntersectingObstructionOn 53 := by
  obtain ⟨H, hsub, hcard⟩ := Finset.exists_subset_card_eq (show 28 ≤ F.card by omega)
  have hHu : ∀ S ∈ H, S.card = 4 := fun S hS => hu S (hsub hS)
  have hHf : IsSunflowerFree H 3 := fun G hG => hf G (hG.trans hsub)
  have hHi : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty :=
    fun S hS T hT => hi S (hsub hS) T (hsub hT)
  have hs := intersecting_twenty_eight_support_le_fifty_three H hHu hHf hHi hcard
  obtain ⟨G, hGc, hGu, hGf, hGi⟩ :=
    exists_intersecting_fin_relabel H 53 4 3 hs hHu hHf hHi
  exact ⟨G, hGc.trans hcard, hGu, hGf, hGi⟩

/-- Exact equivalence for I27; obstruction nonexistence remains an open obligation. -/
theorem intersecting_upper_twenty_seven_iff_no_finite56_obstruction :
    IntersectingRankFourUpper 27 ↔ ¬ FiniteIntersectingObstructionOn 56 := by
  constructor
  · intro hI hobs
    obtain ⟨G, hc, hu, hf, hi⟩ := hobs
    have hb := hI G hu hf hi
    omega
  · intro hn α inst F hu hf hi
    by_contra hnot
    exact hn (finite56_obstruction_of_counterexample F hu hf hi (by omega))

/-- Exact equivalence at the improved capacity, without any computational exclusion. -/
theorem intersecting_upper_twenty_seven_iff_no_finite53_obstruction :
    IntersectingRankFourUpper 27 ↔ ¬ FiniteIntersectingObstructionOn 53 := by
  constructor
  · intro hI hobs
    obtain ⟨G, hc, hu, hf, hi⟩ := hobs
    have hb := hI G hu hf hi
    omega
  · intro hn α inst F hu hf hi
    by_contra hnot
    exact hn (finite53_obstruction_of_counterexample F hu hf hi (by omega))

end FrontierSupportReduction

#print axioms FrontierSupportReduction.finite56_obstruction_of_counterexample
#print axioms FrontierSupportReduction.finite53_obstruction_of_counterexample
#print axioms FrontierSupportReduction.intersecting_upper_twenty_seven_iff_no_finite56_obstruction
#print axioms FrontierSupportReduction.intersecting_upper_twenty_seven_iff_no_finite53_obstruction
