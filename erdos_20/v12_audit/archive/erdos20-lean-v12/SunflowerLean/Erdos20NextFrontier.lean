import SunflowerLean.Erdos20Incidence
import SunflowerLean.Erdos20FiniteReduction
import SunflowerLean.Erdos20LocalStructure
import SunflowerLean.Erdos20TraceStructure

/-! Public assembly of the second-iteration reductions. None of these theorems
asserts the existence of a base satisfying the full sunflower conjecture. -/
namespace Erdos20NextFrontier

open Erdos20BCWConditional Erdos20StrictCore Erdos20Critical
open Erdos20Incidence Erdos20FiniteReduction Erdos20LocalStructure

universe u

/-- Verified recurrence values, not external numerical certificates. -/
theorem refined_three_petals_values :
    [refinedBound 3 0, refinedBound 3 1, refinedBound 3 2,
     refinedBound 3 3, refinedBound 3 4, refinedBound 3 5, refinedBound 3 6] =
    [1, 2, 6, 32, 250, 2492, 29894] := by decide

/-- The sharp six-member rank-two witness amplifies in every even rank. -/
theorem six_power_witness (n : ℕ) :
    UniformFreeWitness.{0} 3 (2 * n) (6 ^ n) := by
  apply tensor_power_witness (by decide)
  exact ⟨Fin 6, inferInstance, twoTriangles,
    twoTriangles_uniform, twoTriangles_sunflower_free, twoTriangles_card⟩

/-- The fixed-rank finite checker can be settled by a structural proof, without
brute-force evaluation of its enormous search space. -/
theorem finite_check_base_four_low_ranks (r : ℕ) (hr : r ≤ 4) :
    obstructionCheck 4 3 r = false := by
  have hn : ¬ FiniteObstruction 4 3 r := by
    rintro ⟨family, hu, hf, hc⟩
    have hb := base_four_critical_rank_ge_five family r hu hf hc
    omega
  simpa [obstructionCheck] using hn

/-- At every base, an eventual tail of finite negative checks is
already equivalent to the exact all-rank bound. -/
theorem uniformBound_iff_eventual_checks {q p : ℕ} (hp : 2 ≤ p) :
    UniformSunflowerBound.{u} q p ↔
      ∃ R : ℕ, ∀ r, R ≤ r → obstructionCheck q p r = false := by
  constructor
  · intro hb
    exact ⟨0, fun r _ => (uniformBound_iff_all_checks_false.{u} q p).mp hb r⟩
  · rintro ⟨R, hR⟩
    apply uniformBound_of_eventual hp
    refine ⟨R, ?_⟩
    intro α inst family r hr hu hf
    exact bound_of_obstructionCheck_eq_false family q p r (hR r hr) hu hf

/-- The full constant-base conjecture, at a fixed petal count, expressed in
canonical finite tests. The remaining quantifier over rank is still infinite. -/
theorem some_base_iff_eventual_checks {p : ℕ} (hp : 2 ≤ p) :
    (∃ q, 0 < q ∧ UniformSunflowerBound.{u} q p) ↔
      ∃ q, 0 < q ∧ ∃ R, ∀ r, R ≤ r → obstructionCheck q p r = false := by
  constructor
  · rintro ⟨q, hq, hb⟩
    exact ⟨q, hq, (uniformBound_iff_eventual_checks hp).mp hb⟩
  · rintro ⟨q, hq, hb⟩
    exact ⟨q, hq, (uniformBound_iff_eventual_checks hp).mpr hb⟩

/-- Both support bounds hold for the same least-rank exact-size family. -/
theorem critical_support_window {α : Type u} [DecidableEq α]
    (family : Finset (Finset α)) (r q p : ℕ)
    (huniform : ∀ S ∈ family, S.card = r)
    (hfree : IsSunflowerFree family p)
    (hlower : LowerRanksBound.{u} q p r)
    (hcard : family.card = q ^ r + 1) :
    r * q < (support family).card ∧
      (support family).card ≤ r * (q ^ r + 1) := by
  have hr := exact_size_rank_pos family r q huniform hcard
  refine ⟨critical_support_card_gt family r q hr huniform hcard ?_,
    exact_size_support_card_bound family r q huniform hcard⟩
  intro x
  have hd := upperStar_bound_of_lowerRanks family r q p huniform hfree hlower
    {x} (Finset.singleton_nonempty x) (by simp; omega)
  simpa [upperStar] using hd

/-- A base-four failure for three petals admits a least-rank finite obstruction
strictly beyond the ranks eliminated by the refined recurrence. -/
theorem base_four_failure_finite_normal_form
    (hfailure : ¬ UniformSunflowerBound.{u} 4 3) :
    ∃ r, 5 ≤ r ∧ LowerRanksBound.{u} 4 3 r ∧ FiniteObstruction 4 3 r := by
  obtain ⟨r, _, hlower, hf⟩ := exists_minimal_finiteObstruction hfailure
  have hr : 5 ≤ r := by
    obtain ⟨family, hu, hfree, hc⟩ := hf
    exact base_four_critical_rank_ge_five family r hu hfree hc
  exact ⟨r, hr, hlower, hf⟩


/-- An eventual estimate with a fixed prefactor, the combined analytic target. -/
def EventualBoundWithPrefactor (q p K R : ℕ) : Prop :=
  ∀ {α : Type u} [DecidableEq α] (F : Finset (Finset α)) (r : ℕ),
    R ≤ r → (∀ S ∈ F, S.card = r) → IsSunflowerFree F p → F.card ≤ K * q ^ r

/-- Simultaneously remove a fixed prefactor and a finite rank cutoff. -/
theorem uniformBound_of_eventual_prefactor {q p K R : ℕ}
    (hq : 0 < q) (hp : 2 ≤ p)
    (hbound : EventualBoundWithPrefactor.{u} q p K R) :
    UniformSunflowerBound.{u} q p := by
  intro α inst F r hu hf
  by_contra hnot
  have hlarge : q ^ r < F.card := Nat.lt_of_not_ge hnot
  have hr : 0 < r := by
    obtain ⟨G, _, hc, hgu, _⟩ := exists_exact_size_free_subfamily F r q p hu hf hlarge
    exact exact_size_rank_pos G r q hgu hc
  have hqrat : 0 < (q : ℚ) := by exact_mod_cast hq
  have hBpos : 0 < (q : ℚ) ^ r := pow_pos hqrat r
  have hlargeRat : (q : ℚ) ^ r < (F.card : ℚ) := by exact_mod_cast hlarge
  let ratio : ℚ := F.card / (q : ℚ) ^ r
  have hratio : 1 < ratio :=
    (lt_div_iff₀ hBpos).mpr (by simpa using hlargeRat)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (K : ℚ) hratio
  have hgrowth : (K : ℚ) < ratio ^ (n + (R + 1)) := by
    have hmono := pow_le_pow_right₀ (le_of_lt hratio) (show n ≤ n + (R + 1) by omega)
    exact hn.trans_le hmono
  obtain ⟨β, instB, G, huG, hfG, hcG⟩ := tensor_power_witness hp
    (show UniformFreeWitness.{u} p r F.card from ⟨α, inst, F, hu, hf, rfl⟩)
    (n + (R + 1))
  have hrank : R ≤ r * (n + (R + 1)) := by
    have h := Nat.le_mul_of_pos_left (n + (R + 1)) hr
    omega
  have hupper := hbound G (r * (n + (R + 1))) hrank huG hfG
  rw [hcG, pow_mul] at hupper
  have hcast : (F.card : ℚ) ^ (n + (R + 1)) ≤
      (K : ℚ) * ((q : ℚ) ^ r) ^ (n + (R + 1)) := by exact_mod_cast hupper
  have hratle : ratio ^ (n + (R + 1)) ≤ K := by
    dsimp [ratio]
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos hBpos _)).mpr hcast
  exact (not_lt_of_ge hratle) hgrowth

/-- Exact equivalence with the more flexible eventual-prefactor target. -/
theorem uniformBound_iff_eventual_prefactor {q p : ℕ}
    (hq : 0 < q) (hp : 2 ≤ p) :
    UniformSunflowerBound.{u} q p ↔ ∃ K R, EventualBoundWithPrefactor.{u} q p K R := by
  constructor
  · intro h
    refine ⟨1, 0, ?_⟩
    intro α inst F r _ hu hf
    simpa using h F r hu hf
  · rintro ⟨K, R, h⟩
    exact uniformBound_of_eventual_prefactor hq hp h

end Erdos20NextFrontier

