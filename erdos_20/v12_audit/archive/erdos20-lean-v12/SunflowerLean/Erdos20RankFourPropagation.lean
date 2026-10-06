import SunflowerLean.Erdos20RankFour
import SunflowerLean.Erdos20SeededBounds

/-! Propagation of the verified rank-four seed by the incidence-defect recurrence.
This is a rank-dependent estimate, not a fixed exponential-base bound. -/
universe u
namespace Erdos20RankFourPropagation
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence Erdos20RankFour

/-- The index counts additional rank above four. -/
def rankFourBound : ℕ → ℕ
  | 0 => 98
  | n + 1 => 2 * ((n + 5) * rankFourBound n - (n + 4))

theorem rankFourBound_pos (n : ℕ) : 0 < rankFourBound n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hm : n + 4 < (n + 5) * rankFourBound n := by nlinarith
    simp only [rankFourBound]
    omega

/-- Every larger rank inherits an unconditional bound from the rank-four theorem. -/
theorem propagated_rank_four_bound
    {α : Type u} [DecidableEq α] (F : Finset (Finset α)) (n : ℕ)
    (hu : ∀ S ∈ F, S.card = n + 4) (hf : IsSunflowerFree F 3) :
    F.card ≤ rankFourBound n := by
  induction n generalizing F with
  | zero => exact rank_four_card_le_ninety_eight F hu hf
  | succ n ih =>
    have hd : ∀ x, (F.filter (fun S => x ∈ S)).card ≤ rankFourBound n := by
      intro x
      have hb := ih (residualLink F {x})
        (by simpa using (residualLink_uniform (core := {x}) hu))
        (residualLink_sunflowerFree hf)
      simpa [card_residualLink,upperStar] using hb
    have hb := card_le_refined_step F (n + 1 + 4) 3 (rankFourBound n)
      (by omega) (rankFourBound_pos n) hu hf hd
    simpa [rankFourBound,Nat.add_assoc] using hb

/-- Kernel-reduced values at ranks four through eight. -/
theorem rankFourBound_values :
    List.map rankFourBound [0,1,2,3,4] = [98,972,11654,163144,2610290] := by
  decide

/-- The stronger seed strictly improves the version-four recurrence at every later rank. -/
theorem rankFourBound_lt_previous (n : ℕ) :
    rankFourBound n < Erdos20SeededBounds.seededBound 20 (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    change 2 * ((n + 5) * rankFourBound n - (n + 4)) <
      2 * ((n + 5) * Erdos20SeededBounds.seededBound 20 (n + 1) - (n + 4))
    have hpos := rankFourBound_pos n
    have hlo : n + 4 < (n + 5) * rankFourBound n := by nlinarith
    have hprod := Nat.mul_lt_mul_of_pos_left ih (show 0 < n + 5 by omega)
    omega

/-- Base four is verified through rank five, including the improved rank-five estimate. -/
theorem rank_at_most_five_base_four
    {α : Type u} [DecidableEq α] (F : Finset (Finset α)) (r : ℕ)
    (hr : r ≤ 5) (hu : ∀ S ∈ F, S.card = r) (hf : IsSunflowerFree F 3) :
    F.card ≤ 4 ^ r := by
  by_cases hsmall : r < 3
  · have hb := refined_sunflower_bound F r 3 (by decide) hu hf
    interval_cases r <;> norm_num [refinedBound] at hb ⊢ <;> omega
  · have hlo : 3 ≤ r := by omega
    interval_cases r
    · have hb := Erdos20SharpTwenty.rank_three_three_petals_card_le_twenty F hu hf
      norm_num; omega
    · have hb := rank_four_card_le_ninety_eight F hu hf
      norm_num; omega
    · have hb := propagated_rank_four_bound F 1 hu hf
      norm_num [rankFourBound] at hb ⊢
      omega

/-- Any failure of the universal base-four estimate must occur at rank at least six. -/
theorem base_four_violating_rank_ge_six
    {α : Type u} [DecidableEq α] (F : Finset (Finset α)) (r : ℕ)
    (hu : ∀ S ∈ F, S.card = r) (hf : IsSunflowerFree F 3)
    (hlarge : 4 ^ r < F.card) : 6 ≤ r := by
  by_contra hn
  have hb := rank_at_most_five_base_four F r (by omega) hu hf
  omega

/-- Base five is verified through rank six. -/
theorem rank_at_most_six_base_five
    {α : Type u} [DecidableEq α] (F : Finset (Finset α)) (r : ℕ)
    (hr : r ≤ 6) (hu : ∀ S ∈ F, S.card = r) (hf : IsSunflowerFree F 3) :
    F.card ≤ 5 ^ r := by
  by_cases hsmall : r ≤ 5
  · have hb := rank_at_most_five_base_four F r hsmall hu hf
    exact hb.trans (Nat.pow_le_pow_left (by decide : 4 ≤ 5) r)
  · have he : r = 6 := by omega
    subst r
    have hb := propagated_rank_four_bound F 2 hu hf
    norm_num [rankFourBound] at hb ⊢
    omega

/-- Any failure of the universal base-five estimate must occur at rank at least seven. -/
theorem base_five_violating_rank_ge_seven
    {α : Type u} [DecidableEq α] (F : Finset (Finset α)) (r : ℕ)
    (hu : ∀ S ∈ F, S.card = r) (hf : IsSunflowerFree F 3)
    (hlarge : 5 ^ r < F.card) : 7 ≤ r := by
  by_contra hn
  have hb := rank_at_most_six_base_five F r (by omega) hu hf
  omega

end Erdos20RankFourPropagation
