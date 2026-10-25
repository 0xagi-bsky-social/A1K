import SunflowerLean.Erdos20SharpTwenty
import SunflowerLean.Erdos20TripleReduction
import SunflowerLean.Erdos20TripleWitness
import SunflowerLean.Erdos20SeededBounds
import SunflowerLean.Erdos20ExtremalSupport

/-! The sharp triple maximum, its finite-checker consequence, and propagation.
The classical sharp value is not a solution in arbitrary rank. -/
universe u
namespace Erdos20V4Frontier
open Erdos20SharpTwenty Erdos20TripleReduction Erdos20TripleWitness Erdos20SeededBounds

theorem triple_bound_twenty : TripleBoundTwenty.{u} :=
  fun {_} [_] F hu hf => rank_three_three_petals_card_le_twenty F hu hf

/-- The universal upper estimate is attained on a twelve-point ambient type. -/
theorem sharp_triple_maximum : TripleBoundTwenty.{u} ∧
    ∃ F : Finset (Finset (Fin 12)),
      (∀ S ∈ F, S.card = 3) ∧ IsSunflowerFree F 3 ∧ F.card = 20 :=
  ⟨triple_bound_twenty,
    twentyTriples, twentyTriples_uniform, twentyTriples_sunflower_free, twentyTriples_card⟩

/-- The forcing threshold is twenty-one, while the free maximum is twenty. -/
theorem twenty_one_triples_force_sunflower {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S ∈ F, S.card = 3) (hc : 21 ≤ F.card) :
    ∃ H ⊆ F, IsSunflower H 3 := by
  classical
  by_contra hnot
  have hf : IsSunflowerFree F 3 := by
    intro H hH hs
    exact hnot ⟨H,hH,hs⟩
  have hb := rank_three_three_petals_card_le_twenty F hu hf
  omega

theorem no_twenty_one_on_fifteen : ¬ TwentyOneOnFifteen :=
  triple_bound_twenty_iff.mp triple_bound_twenty.{0}

/-- A structural proof of the Boolean value, without exhaustive evaluation. -/
theorem sharp_triple_check_false : sharpTripleCheck = false :=
  triple_bound_twenty_iff_check_false.mp triple_bound_twenty.{0}

theorem sharp_seed_bound {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (n : ℕ)
    (hu : ∀ S ∈ F, S.card = n + 3) (hf : IsSunflowerFree F 3) :
    F.card ≤ seededBound 20 n :=
  seeded_sunflower_bound 20 (by decide)
    (fun {_} [_] F hu hf => rank_three_three_petals_card_le_twenty F hu hf)
    F n hu hf

theorem sharp_seed_values :
    List.map (seededBound 20) [0, 1, 2, 3, 4] = [20, 154, 1532, 18374, 257224] := by
  decide

/-- The explicit extremal family uses all twelve ambient points. -/
theorem twentyTriples_support_card :
    (Erdos20BCWConditional.support twentyTriples).card = 12 := by
  decide

/-- The lower endpoint of the extremal support window is attained. -/
theorem sharp_minimum_extremal_support :
    (∀ {α : Type u} [DecidableEq α] (F : Finset (Finset α)),
      (∀ S ∈ F, S.card = 3) → IsSunflowerFree F 3 → F.card = 20 →
      12 ≤ (Erdos20BCWConditional.support F).card) ∧
    ∃ F : Finset (Finset (Fin 12)),
      (∀ S ∈ F, S.card = 3) ∧ IsSunflowerFree F 3 ∧ F.card = 20 ∧
      (Erdos20BCWConditional.support F).card = 12 := by
  refine ⟨?_, twentyTriples, twentyTriples_uniform,
    twentyTriples_sunflower_free, twentyTriples_card, twentyTriples_support_card⟩
  intro α _ F hu hf hc
  exact (Erdos20ExtremalSupport.extremal_support_card_window F hu hf hc).1

end Erdos20V4Frontier
