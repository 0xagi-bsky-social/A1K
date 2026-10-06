import SunflowerLean.Erdos20Substitution
import SunflowerLean.Erdos20SeededBounds
import SunflowerLean.Erdos20FiniteReduction

/-! The new lower witness and upper estimates in the existing finite interface. -/
universe u
namespace Erdos20V3Frontier
open Erdos20StrictCore Erdos20Critical Erdos20FiniteReduction
open Erdos20Substitution Erdos20Incidence

theorem base_three_rank_nine_obstruction : FiniteObstruction 3 3 9 := by
  apply finiteObstruction_of_counterexample twentyThousand 3 3 9
    twentyThousand_uniform twentyThousand_sunflower_free
  rw [twentyThousand_card]
  norm_num

/-- This Boolean result is deduced from a structural witness, not from
exhaustive execution of the enormous finite search. -/
theorem base_three_rank_nine_check : obstructionCheck 3 3 9 = true :=
  (obstructionCheck_eq_true_iff.{0} 3 3 9).mpr
    ((rankCounterexample_iff_finiteObstruction.{0} 3 3 9).mpr base_three_rank_nine_obstruction)

theorem base_three_failure_all_universes : ¬ UniformSunflowerBound.{u} 3 3 := by
  intro h
  exact (uniformBound_iff_no_finiteObstruction 3 3).mp h 9 base_three_rank_nine_obstruction

/-- The integer-base obstruction is independent of the ambient universe. -/
theorem base_ge_four_all_universes {q : ℕ} (h : UniformSunflowerBound.{u} q 3) :
    4 ≤ q := by
  apply uniformBound_base_ge_four
  apply (uniformBound_iff_no_finiteObstruction q 3).mpr
  exact (uniformBound_iff_no_finiteObstruction q 3).mp h

/-- No base-three obstruction exists through rank three. -/
theorem base_three_low_ranks {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (r : ℕ) (hr : r ≤ 3)
    (hu : ∀ S ∈ F, S.card = r) (hf : IsSunflowerFree F 3) : F.card ≤ 3 ^ r := by
  interval_cases r
  · have hb := refined_sunflower_bound F 0 3 (by decide) hu hf
    simpa [refinedBound] using hb
  · have hb := refined_sunflower_bound F 1 3 (by decide) hu hf
    norm_num [refinedBound] at hb ⊢
    omega
  · have hb := rank_two_three_petals_card_le_six F hu hf
    norm_num
    omega
  · have hb := Erdos20RankThreeEven.rank_three_three_petals_card_le_twenty_two F hu hf
    norm_num
    omega

/-- A least-rank failure of base three occurs between ranks four and nine,
with the previously verified lower-rank and exact finite-obstruction properties. -/
theorem least_base_three_failure_window :
    ∃ r, 4 ≤ r ∧ r ≤ 9 ∧ LowerRanksBound.{0} 3 3 r ∧ FiniteObstruction 3 3 r := by
  obtain ⟨r, _, hlower, hfinite⟩ :=
    exists_minimal_finiteObstruction not_uniformBound_three_three
  have hlo : 4 ≤ r := by
    by_contra hn
    obtain ⟨F, hu, hf, hc⟩ := hfinite
    have hb := base_three_low_ranks F r (by omega) hu hf
    omega
  have hhi : r ≤ 9 := by
    by_contra hn
    have hb := hlower twentyThousand 9 (by omega) twentyThousand_uniform
      twentyThousand_sunflower_free
    rw [twentyThousand_card] at hb
    norm_num at hb
  exact ⟨r, hlo, hhi, hlower, hfinite⟩

end Erdos20V3Frontier
