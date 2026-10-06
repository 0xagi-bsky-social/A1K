import SunflowerLean.Erdos20V10BoundaryReduction
import SunflowerLean.Erdos20V10Profile54SeventeenCap

namespace Erdos20V10FiniteEndgame
open Erdos20BCWConditional Erdos20DegreeCongruences Erdos20V8Targets
open Erdos20V9Census Erdos20ExtremalSupport Erdos20V10BoundaryReduction
open Erdos20V10Profile54Seventeen

/-- Incidence of the sparse degree17 class sharpens the remaining support
range to exactly17 or18 points. No finite-search result is assumed. -/
theorem conditional_eighty_one_support_seventeen_or_eighteen
    (hI : IntersectingRankFourUpper 27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3) (hc : F.card=81) :
    (support F).card=17 ∨ (support F).card=18 := by
  classical
  obtain ⟨hd,hslo,_⟩ := conditional_eighty_one_min_degree_and_support hI F hu hf hc
  have hm : ∀ R ∈ F, 54 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card := by
    intro R hR
    have hh := meeting_lower_bound_of_intersecting_upper hI F hu hf R hR
    omega
  have hcap := degree_seventeen_member_card_le_one F hu hf hm
  have hcount := degree_predicate_incidence_le F (fun d => d=17) 1 hcap
  change (∑ x ∈ degreeClass F 17, degree F x) ≤ 1 * F.card at hcount
  rw [degreeClass_sum] at hcount
  have ha : (degreeClass F 17).card ≤ 4 := by omega
  have htotal : (∑ x ∈ support F, degree F x)=324 := by
    have hh := support_degree_sum F 4 hu
    simpa [hc,Nat.mul_comm] using hh
  have hones : (∑ x ∈ support F, if degree F x=17 then 1 else 0) =
      (degreeClass F 17).card := by
    simp only [degreeClass,Finset.card_eq_sum_ones,Finset.sum_filter]
  have hsum : 18 * (support F).card ≤ 324 + (degreeClass F 17).card := by
    calc
      _ = ∑ _x ∈ support F, 18 := by simp [Nat.mul_comm]
      _ ≤ ∑ x ∈ support F, (degree F x + if degree F x=17 then 1 else 0) := by
        apply Finset.sum_le_sum
        intro x hx
        have hh := hd x hx
        split_ifs <;> omega
      _ = _ := by rw [Finset.sum_add_distrib,htotal,hones]
  omega

/-- Finite-support endgame: given I27, a universal80 ceiling for families on
at most18 supported points suffices for the unrestricted80 ceiling.
Both unresolved inputs remain explicit ordinary theorem arguments. -/
theorem unrestricted_eighty_of_small_support_eighty
    (hI : IntersectingRankFourUpper 27)
    (hsmall : ∀ {α : Type} [DecidableEq α] (F : Finset (Finset α)),
      (∀ R ∈ F, R.card=4) → IsSunflowerFree F 3 →
      (support F).card≤18 → F.card≤80) : RankFourUpper 80 := by
  intro α inst F hu hf
  have h81 := Erdos20V9Final.unrestricted_upper_eighty_one_of_intersecting_twenty_seven hI F hu hf
  by_contra hn
  have hc : F.card=81 := by omega
  have hs := conditional_eighty_one_support_seventeen_or_eighteen hI F hu hf hc
  have h80 := hsmall F hu hf (by omega)
  omega

end Erdos20V10FiniteEndgame
