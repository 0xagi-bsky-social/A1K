import SunflowerLean.Erdos20Substitution
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Iterated intersecting-block witnesses and the classical square-root-of-ten
barrier for real exponential bases. The combinatorial construction is classical;
this module supplies an exact checked iteration and asymptotic interface. -/
namespace Erdos20IteratedLower

open Erdos20Substitution Erdos20TripleWitness Erdos20LocalStructure

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem intersecting_substitution
    (F : Finset (Finset α)) (G : Finset (Finset β))
    (hintF : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty)
    (hintG : ∀ A ∈ G, ∀ B ∈ G, (A ∩ B).Nonempty) :
    ∀ A ∈ substitution F G, ∀ B ∈ substitution F G, (A ∩ B).Nonempty := by
  classical
  intro A hA B hB
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hB
  have h := hintF _ a.1.property _ b.1.property
  rw [← support_inter_encode a b hintG] at h
  exact Finset.Nonempty.of_image h

/-- The intersecting variant is needed to iterate the block operation. -/
def IntersectingFreeWitness (r N : ℕ) : Prop :=
  ∃ (α : Type) (_ : DecidableEq α) (F : Finset (Finset α)),
    (∀ S ∈ F, S.card = r) ∧ IsSunflowerFree F 3 ∧ F.card = N ∧
    (∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)

theorem intersecting_witness_substitution {r s N M : ℕ}
    (hF : IntersectingFreeWitness r N) (hG : IntersectingFreeWitness s M) :
    IntersectingFreeWitness (r * s) (N * M ^ r) := by
  classical
  obtain ⟨α, instα, F, huF, hfF, hcF, hiF⟩ := hF
  obtain ⟨β, instβ, G, huG, hfG, hcG, hiG⟩ := hG
  refine ⟨α × β, inferInstance, substitution F G,
    uniform_substitution F G r s huF huG,
    sunflowerFree_substitution F G r s huF huG hfF hfG hiG, ?_,
    intersecting_substitution F G hiF hiG⟩
  rw [card_substitution F G r huF, hcF, hcG]
  intro B hB
  exact (hiG B hB B hB).mono (Finset.inter_subset_left)

def singletonFamily : Finset (Finset (Fin 1)) := {{0}}

theorem singleton_intersecting_witness : IntersectingFreeWitness 1 1 := by
  refine ⟨Fin 1, inferInstance, singletonFamily, ?_, ?_, ?_, ?_⟩
  · simp [singletonFamily]
  · intro H hsub hsun
    have hcard := Finset.card_le_card hsub
    simp [singletonFamily] at hcard
    have hs := hsun.1
    omega
  · decide
  · simp [singletonFamily]

theorem ten_intersecting_witness : IntersectingFreeWitness 3 10 :=
  ⟨Fin 6, inferInstance, tenTriples, tenTriples_uniform,
    tenTriples_sunflower_free, tenTriples_card, tenTriples_intersecting⟩

/-- Integer exponent of the exact iterated cardinality. -/
def iterationExponent : ℕ → ℕ
  | 0 => 0
  | n + 1 => iterationExponent n + 3 ^ n

theorem iterationExponent_twice_add_one (n : ℕ) :
    2 * iterationExponent n + 1 = 3 ^ n := by
  induction n with
  | zero => simp [iterationExponent]
  | succ n ih =>
    rw [iterationExponent, pow_succ]
    omega

theorem iterationExponent_closed (n : ℕ) :
    iterationExponent n = (3 ^ n - 1) / 2 := by
  have h := iterationExponent_twice_add_one n
  omega

theorem iterationExponent_ge (n : ℕ) : n ≤ iterationExponent n := by
  induction n with
  | zero => simp [iterationExponent]
  | succ n ih =>
    have hpos : 0 < 3 ^ n := by positivity
    simp only [iterationExponent]
    omega

theorem iterated_intersecting_witness (n : ℕ) :
    IntersectingFreeWitness (3 ^ n) (10 ^ iterationExponent n) := by
  induction n with
  | zero => simpa [iterationExponent] using singleton_intersecting_witness
  | succ n ih =>
    have h := intersecting_witness_substitution ih ten_intersecting_witness
    simpa only [iterationExponent, pow_succ, pow_add] using h

theorem iterated_intersecting_closed_witness (n : ℕ) :
    IntersectingFreeWitness (3 ^ n) (10 ^ ((3 ^ n - 1) / 2)) := by
  rw [← iterationExponent_closed]
  exact iterated_intersecting_witness n

/-- Any intersecting witness can be copied onto two disjoint supports. -/
theorem double_intersecting_witness {r N : ℕ}
    (h : IntersectingFreeWitness r N) : UniformFreeWitness.{0} 3 r (2 * N) := by
  classical
  obtain ⟨α, inst, G, huG, hfG, hcG, hiG⟩ := h
  let F : Finset (Finset (Fin 2)) := {{0}, {1}}
  have huF : ∀ S ∈ F, S.card = 1 := by simp [F]
  have hcF : F.card = 2 := by decide
  have hfF : IsSunflowerFree F 3 := by
    intro H hsub hsun
    have hc := Finset.card_le_card hsub
    have hs := hsun.1
    rw [hcF] at hc
    omega
  have hnG : ∀ B ∈ G, B.Nonempty := fun B hB =>
    (hiG B hB B hB).mono Finset.inter_subset_left
  refine ⟨Fin 2 × α, inferInstance, substitution F G, ?_, ?_, ?_⟩
  · simpa using uniform_substitution F G 1 r huF huG
  · exact sunflowerFree_substitution F G 1 r huF huG hfF hfG hiG
  · rw [card_substitution F G 1 huF hnG, hcF, hcG, pow_one]

theorem iterated_double_witness (n : ℕ) :
    UniformFreeWitness.{0} 3 (3 ^ n) (2 * 10 ^ ((3 ^ n - 1) / 2)) :=
  double_intersecting_witness (iterated_intersecting_closed_witness n)

/-- A real exponential upper bound with one fixed prefactor and rank cutoff. -/
def EventualRealBound (b K : ℝ) (R : ℕ) : Prop :=
  ∀ {α : Type} [DecidableEq α] (F : Finset (Finset α)) (r : ℕ),
    R ≤ r → (∀ S ∈ F, S.card = r) → IsSunflowerFree F 3 →
    (F.card : ℝ) ≤ K * b ^ r

/-- The checked finite witnesses impose their exact numerical inequalities
on every proposed eventual real-base estimate. -/
theorem iterated_bound_constraint {b K : ℝ} {R : ℕ}
    (hbound : EventualRealBound b K R) (n : ℕ) (hR : R ≤ 3 ^ n) :
    (10 : ℝ) ^ iterationExponent n ≤ K * b ^ (3 ^ n) := by
  obtain ⟨α, inst, F, hu, hf, hc, hi⟩ := iterated_intersecting_witness n
  have h := hbound F _ hR hu hf
  rw [hc] at h
  exact_mod_cast h

/-- A fixed prefactor and an arbitrary rank cutoff cannot lower the
classical square-root-of-ten barrier. -/
theorem iterated_real_bound_sq_ge_ten {b K : ℝ} {R : ℕ}
    (hb : 0 < b)
    (hbound : ∀ n, R ≤ 3 ^ n →
      (10 : ℝ) ^ iterationExponent n ≤ K * b ^ (3 ^ n)) : 10 ≤ b ^ 2 := by
  by_contra hnot
  have hless : b ^ 2 < 10 := lt_of_not_ge hnot
  have hb2 : 0 < b ^ 2 := pow_pos hb 2
  have hratio : 1 < (10 : ℝ) / b ^ 2 := by
    exact (lt_div_iff₀ hb2).mpr (by simpa using hless)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (K * b) hratio
  let m := max n R
  have he : n ≤ iterationExponent m :=
    (le_max_left n R).trans (iterationExponent_ge m)
  have hR : R ≤ 3 ^ m := by
    have hx := iterationExponent_twice_add_one m
    have hy := iterationExponent_ge m
    have hz : R ≤ m := le_max_right n R
    omega
  have hupper := hbound m hR
  have hpow : b ^ (3 ^ m) = b * (b ^ 2) ^ iterationExponent m := by
    rw [← iterationExponent_twice_add_one m, pow_add, pow_mul, pow_one]
    ring
  rw [hpow] at hupper
  have hratle : ((10 : ℝ) / b ^ 2) ^ iterationExponent m ≤ K * b := by
    rw [div_pow]
    apply (div_le_iff₀ (pow_pos hb2 _)).mpr
    nlinarith [hupper]
  have hmon : ((10 : ℝ) / b ^ 2) ^ n ≤
      ((10 : ℝ) / b ^ 2) ^ iterationExponent m :=
    pow_le_pow_right₀ (le_of_lt hratio) he
  exact (not_lt_of_ge (hmon.trans hratle)) hn

theorem eventual_real_bound_sq_ge_ten {b K : ℝ} {R : ℕ}
    (hb : 0 < b) (hbound : EventualRealBound b K R) : 10 ≤ b ^ 2 :=
  iterated_real_bound_sq_ge_ten hb (iterated_bound_constraint hbound)

theorem eventual_real_bound_ge_sqrt_ten {b K : ℝ} {R : ℕ}
    (hb : 0 < b) (hbound : EventualRealBound b K R) : Real.sqrt 10 ≤ b :=
  (Real.sqrt_le_left (le_of_lt hb)).mpr (eventual_real_bound_sq_ge_ten hb hbound)

/-- Negating the universal estimate gives arbitrarily high-rank finite
counterexamples below the square-root-of-ten base. -/
theorem below_sqrt_ten_fails_eventually {b K : ℝ} {R : ℕ}
    (hb : 0 < b) (hsmall : b < Real.sqrt 10) : ¬ EventualRealBound b K R := by
  intro hbound
  exact (not_lt_of_ge (eventual_real_bound_ge_sqrt_ten hb hbound)) hsmall

/-- A counterexample is always available among the explicit iterated
witnesses themselves, above any requested rank cutoff. -/
theorem below_sqrt_ten_iterated_counterexample {b K : ℝ} (R : ℕ)
    (hb : 0 < b) (hsmall : b < Real.sqrt 10) :
    ∃ n, R ≤ 3 ^ n ∧ K * b ^ (3 ^ n) < (10 : ℝ) ^ iterationExponent n := by
  by_contra hnot
  push_neg at hnot
  have hsq := iterated_real_bound_sq_ge_ten hb hnot
  have hle : Real.sqrt 10 ≤ b := (Real.sqrt_le_left (le_of_lt hb)).mpr hsq
  exact (not_lt_of_ge hle) hsmall

theorem below_sqrt_ten_finite_counterexample {b K : ℝ} (R : ℕ)
    (hb : 0 < b) (hsmall : b < Real.sqrt 10) :
    ∃ (α : Type) (_ : DecidableEq α) (F : Finset (Finset α)) (r : ℕ),
      R ≤ r ∧ (∀ S ∈ F, S.card = r) ∧ IsSunflowerFree F 3 ∧
      K * b ^ r < (F.card : ℝ) := by
  obtain ⟨n, hR, hlarge⟩ := below_sqrt_ten_iterated_counterexample R hb hsmall
  obtain ⟨α, inst, F, hu, hf, hc, hi⟩ := iterated_intersecting_witness n
  refine ⟨α, inst, F, 3 ^ n, hR, hu, hf, ?_⟩
  rw [hc]
  exact_mod_cast hlarge

end Erdos20IteratedLower
