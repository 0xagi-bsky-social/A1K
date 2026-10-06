import SunflowerLean.Erdos20RankThreeEven

/-! Propagate any verified rank-three estimate by incidence-defect counting. -/
universe u

namespace Erdos20SeededBounds
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence

/-- The index counts the additional rank above three. -/
def seededBound (B : ℕ) : ℕ → ℕ
  | 0 => B
  | n + 1 => 2 * ((n + 4) * seededBound B n - (n + 3))

theorem seededBound_pos (B n : ℕ) (hB : 0 < B) :
    0 < seededBound B n := by
  induction n with
  | zero => exact hB
  | succ n ih =>
    have hm : n + 3 < (n + 4) * seededBound B n := by nlinarith
    simp only [seededBound]
    omega

/-- A rank-three theorem is enough to seed a bound at every larger rank. -/
theorem seeded_sunflower_bound (B : ℕ) (hB : 0 < B)
    (hbase : ∀ {α : Type u} [DecidableEq α] (F : Finset (Finset α)),
      (∀ S ∈ F, S.card = 3) → IsSunflowerFree F 3 → F.card ≤ B)
    {α : Type u} [DecidableEq α] (F : Finset (Finset α)) (n : ℕ)
    (hu : ∀ S ∈ F, S.card = n + 3) (hf : IsSunflowerFree F 3) :
    F.card ≤ seededBound B n := by
  induction n generalizing F with
  | zero => exact hbase F hu hf
  | succ n ih =>
    have hd : ∀ x, (F.filter (fun S => x ∈ S)).card ≤ seededBound B n := by
      intro x
      have hb := ih (residualLink F {x})
        (by simpa using (residualLink_uniform (core := {x}) hu))
        (residualLink_sunflowerFree hf)
      simpa [card_residualLink, upperStar] using hb
    have hb := card_le_refined_step F (n + 1 + 3) 3 (seededBound B n)
      (by omega) (seededBound_pos B n hB) hu hf hd
    simpa [seededBound, Nat.add_assoc] using hb

/-- First propagation of the twenty-three bound, before the parity refinement. -/
theorem triple_trace_seed_bound {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (n : ℕ)
    (hu : ∀ S ∈ F, S.card = n + 3) (hf : IsSunflowerFree F 3) :
    F.card ≤ seededBound 23 n :=
  seeded_sunflower_bound 23 (by decide)
    (fun {_} [_] F hu hf => Erdos20RankThree.rank_three_three_petals_card_le_twenty_three F hu hf)
    F n hu hf

theorem seeded_bound_values :
    List.map (seededBound 23) [0, 1, 2, 3] = [23, 178, 1772, 21254] := by
  decide

/-- Propagating the endpoint-exclusion refinement. -/
theorem parity_seed_bound {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (n : ℕ)
    (hu : ∀ S ∈ F, S.card = n + 3) (hf : IsSunflowerFree F 3) :
    F.card ≤ seededBound 22 n :=
  seeded_sunflower_bound 22 (by decide)
    (fun {_} [_] F hu hf => Erdos20RankThreeEven.rank_three_three_petals_card_le_twenty_two F hu hf)
    F n hu hf

theorem parity_seed_values :
    List.map (seededBound 22) [0, 1, 2, 3, 4] = [22, 170, 1692, 20294, 284104] := by
  decide

end Erdos20SeededBounds
