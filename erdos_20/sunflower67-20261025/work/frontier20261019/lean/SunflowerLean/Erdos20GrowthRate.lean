import SunflowerLean.Erdos20FiniteReduction
import SunflowerLean.Erdos20IteratedLower
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Canonical extremal cardinalities and asymptotic exponential growth

The finite maximum is explicit and independent of the ambient universe.
Its logarithmic rate is superadditive. Boundedness of the normalized rates
is an equivalent form of the open exponential-bound question, not an extra
claim that the question has been solved.
-/
namespace Erdos20GrowthRate

open Erdos20BCWConditional Erdos20StrictCore Erdos20FiniteReduction
  Erdos20LocalStructure Erdos20IteratedLower
open Set Filter Topology

universe u

/-- The classical factorial bound gives a sufficient canonical ground-set size. -/
def groundSize (p r : ℕ) : ℕ := r * ((p - 1) ^ r * r.factorial)

/-- All admissible families in that finite ground set. -/
noncomputable def admissible (p r : ℕ) :
    Finset (Finset (Finset (Fin (groundSize p r)))) := by
  classical
  exact Finset.univ.filter fun F =>
    (∀ S ∈ F, S.card = r) ∧ IsSunflowerFree F p

/-- The exact finite extremal cardinality, with no ambient universe parameter. -/
noncomputable def extremal (p r : ℕ) : ℕ := (admissible p r).sup Finset.card

theorem mem_admissible_iff (p r : ℕ)
    (F : Finset (Finset (Fin (groundSize p r)))) :
    F ∈ admissible p r ↔ (∀ S ∈ F, S.card = r) ∧ IsSunflowerFree F p := by
  classical
  simp [admissible]

theorem finite_representative {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (p r : ℕ)
    (hu : ∀ S ∈ F, S.card = r) (hf : IsSunflowerFree F p) :
    ∃ G ∈ admissible p r, G.card = F.card := by
  have hc := Erdos20Classical.erdos_rado_factorial_bound F r p hu hf
  have hs : (support F).card ≤ groundSize p r := by
    have h := Finset.card_biUnion_le_card_mul F id r
      (fun S hS => le_of_eq (hu S hS))
    change (F.biUnion id).card ≤ _
    exact h.trans (by simpa [groundSize, Nat.mul_comm] using Nat.mul_le_mul_right r hc)
  obtain ⟨G, hG, huG, hfG⟩ := exists_fin_relabel F (groundSize p r) r p hs hu hf
  exact ⟨G, (mem_admissible_iff p r G).mpr ⟨huG, hfG⟩, hG⟩

/-- Every family on every ambient type is bounded by this same finite maximum. -/
theorem card_le_extremal {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (p r : ℕ)
    (hu : ∀ S ∈ F, S.card = r) (hf : IsSunflowerFree F p) :
    F.card ≤ extremal p r := by
  obtain ⟨G, hG, hcG⟩ := finite_representative F p r hu hf
  rw [← hcG]
  exact Finset.le_sup hG

theorem admissible_nonempty {p : ℕ} (hp : 1 ≤ p) (r : ℕ) :
    (admissible p r).Nonempty := by
  classical
  refine ⟨∅, (mem_admissible_iff p r ∅).mpr ⟨by simp, ?_⟩⟩
  intro H hH hsun
  have he : H = ∅ := Finset.subset_empty.mp hH
  have hc := hsun.1
  simp [he] at hc
  omega

/-- The maximum is attained in the displayed finite ground set. -/
theorem extremal_attained {p : ℕ} (hp : 1 ≤ p) (r : ℕ) :
    ∃ F : Finset (Finset (Fin (groundSize p r))),
      (∀ S ∈ F, S.card = r) ∧ IsSunflowerFree F p ∧ F.card = extremal p r := by
  obtain ⟨F, hF, hc⟩ := Finset.exists_mem_eq_sup
    (admissible p r) (admissible_nonempty hp r) Finset.card
  exact ⟨F, ((mem_admissible_iff p r F).mp hF).1,
    ((mem_admissible_iff p r F).mp hF).2, hc.symm⟩

theorem extremal_factorial_bound (p r : ℕ) :
    extremal p r ≤ (p - 1) ^ r * r.factorial := by
  classical
  apply Finset.sup_le
  intro F hF
  obtain ⟨hu, hf⟩ := (mem_admissible_iff p r F).mp hF
  exact Erdos20Classical.erdos_rado_factorial_bound F r p hu hf

theorem singleton_rank_witness {p : ℕ} (hp : 2 ≤ p) (r : ℕ) :
    UniformFreeWitness.{0} p r 1 := by
  refine ⟨Fin r, inferInstance, {Finset.univ}, ?_, ?_, by simp⟩
  · simp
  · intro H hH hsun
    have hc : H.card ≤ 1 := by simpa using Finset.card_le_card hH
    have he := hsun.1
    omega

theorem witness_le_extremal {p r N : ℕ} (h : UniformFreeWitness.{u} p r N) :
    N ≤ extremal p r := by
  obtain ⟨α, inst, F, hu, hf, hc⟩ := h
  simpa [hc] using card_le_extremal F p r hu hf

theorem extremal_pos {p : ℕ} (hp : 2 ≤ p) (r : ℕ) : 0 < extremal p r :=
  lt_of_lt_of_le (by decide) (witness_le_extremal (singleton_rank_witness hp r))

theorem extremal_zero {p : ℕ} (hp : 2 ≤ p) : extremal p 0 = 1 := by
  have h := extremal_factorial_bound p 0
  have hpos := extremal_pos hp 0
  simp only [pow_zero, Nat.factorial_zero, mul_one] at h
  omega

/-- Tensor products establish genuine supermultiplicativity at every rank. -/
theorem extremal_supermultiplicative {p : ℕ} (hp : 2 ≤ p) (r s : ℕ) :
    extremal p r * extremal p s ≤ extremal p (r + s) := by
  obtain ⟨F, huF, hfF, hcF⟩ := extremal_attained (by omega : 1 ≤ p) r
  obtain ⟨G, huG, hfG, hcG⟩ := extremal_attained (by omega : 1 ≤ p) s
  exact witness_le_extremal (tensor_witness
    ⟨_, inferInstance, F, huF, hfF, hcF⟩ ⟨_, inferInstance, G, huG, hfG, hcG⟩)

/-- A pointwise bound for the canonical sequence is exactly the literal
universal bound, in every ambient universe. -/
theorem uniformBound_iff_extremal_le {p q : ℕ} (hp : 2 ≤ p) :
    UniformSunflowerBound.{u} q p ↔ ∀ r, extremal p r ≤ q ^ r := by
  constructor
  · intro hb r
    obtain ⟨F, hu, hf, hc⟩ := extremal_attained (by omega : 1 ≤ p) r
    let e : Fin (groundSize p r) ↪ ULift.{u} (Fin (groundSize p r)) :=
      Equiv.ulift.symm.toEmbedding
    have h := hb (mapFamily e F) r (uniform_mapFamily e F r hu)
      ((isSunflowerFree_mapFamily_iff e F p).mpr hf)
    simpa [card_mapFamily, hc] using h
  · intro hb α inst F r hu hf
    exact (card_le_extremal F p r hu hf).trans (hb r)

/-- Logarithm of the exact maximum. -/
noncomputable def logExtremal (p r : ℕ) : ℝ := Real.log (extremal p r)

/-- Rank zero contributes zero, using the field convention `x / 0 = 0`. -/
noncomputable def normalizedLog (p r : ℕ) : ℝ := logExtremal p r / r

/-- The substantive unresolved finiteness condition for a fixed petal count. -/
def FiniteGrowth (p : ℕ) : Prop := BddAbove (Set.range (normalizedLog p))

/-- Meaningful as the extremal growth exponent only under `FiniteGrowth p`.
Without boundedness the real supremum has no asserted growth interpretation. -/
noncomputable def entropy (p : ℕ) : ℝ := sSup (Set.range (normalizedLog p))

theorem logExtremal_nonneg {p : ℕ} (hp : 2 ≤ p) (r : ℕ) :
    0 ≤ logExtremal p r := by
  apply Real.log_nonneg
  exact_mod_cast extremal_pos hp r

theorem normalizedLog_nonneg {p : ℕ} (hp : 2 ≤ p) (r : ℕ) :
    0 ≤ normalizedLog p r :=
  div_nonneg (logExtremal_nonneg hp r) (Nat.cast_nonneg r)

theorem logExtremal_superadditive {p : ℕ} (hp : 2 ≤ p) (r s : ℕ) :
    logExtremal p r + logExtremal p s ≤ logExtremal p (r + s) := by
  have hr : (0 : ℝ) < extremal p r := by exact_mod_cast extremal_pos hp r
  have hs : (0 : ℝ) < extremal p s := by exact_mod_cast extremal_pos hp s
  have h := Real.log_le_log (mul_pos hr hs)
    (show (extremal p r : ℝ) * extremal p s ≤ extremal p (r + s) by
      exact_mod_cast extremal_supermultiplicative hp r s)
  simpa [logExtremal, Real.log_mul (ne_of_gt hr) (ne_of_gt hs)] using h

theorem neg_logExtremal_subadditive {p : ℕ} (hp : 2 ≤ p) :
    Subadditive (fun r => -logExtremal p r) := by
  intro r s
  have h := logExtremal_superadditive hp r s
  linarith

theorem normalizedLog_le_entropy {p : ℕ} (hfin : FiniteGrowth p) (r : ℕ) :
    normalizedLog p r ≤ entropy p :=
  le_csSup hfin ⟨r, rfl⟩

theorem entropy_le_iff {p : ℕ} (hfin : FiniteGrowth p) (c : ℝ) :
    entropy p ≤ c ↔ ∀ r, normalizedLog p r ≤ c := by
  constructor
  · intro h r
    exact (normalizedLog_le_entropy hfin r).trans h
  · intro h
    exact csSup_le (Set.range_nonempty _) (by rintro x ⟨r, rfl⟩; exact h r)

theorem entropy_nonneg {p : ℕ} (hfin : FiniteGrowth p) : 0 ≤ entropy p := by
  have h := normalizedLog_le_entropy hfin 0
  simpa [normalizedLog] using h

/-- Normalized logarithms express an exact real-base bound, including rank zero. -/
theorem real_bound_iff_normalizedLog_le {p : ℕ} (hp : 2 ≤ p)
    {b : ℝ} (hb : 0 < b) :
    (∀ r, (extremal p r : ℝ) ≤ b ^ r) ↔
      ∀ r, normalizedLog p r ≤ Real.log b := by
  constructor
  · intro h r
    by_cases hr : r = 0
    · subst r
      have h₁ := h 1
      have he : (1 : ℝ) ≤ extremal p 1 := by exact_mod_cast extremal_pos hp 1
      have hb₁ : 1 ≤ b := by simpa using he.trans h₁
      simpa [normalizedLog] using Real.log_nonneg hb₁
    · have hpos : (0 : ℝ) < extremal p r := by exact_mod_cast extremal_pos hp r
      have hl := Real.log_le_log hpos (h r)
      rw [Real.log_pow] at hl
      exact (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hr : (0 : ℝ) < r)).mpr
        (by simpa [logExtremal, mul_comm] using hl)
  · intro h r
    by_cases hr : r = 0
    · simp [hr, extremal_zero hp]
    · have hpos : (0 : ℝ) < extremal p r := by exact_mod_cast extremal_pos hp r
      apply (Real.log_le_log_iff hpos (pow_pos hb r)).mp
      rw [Real.log_pow]
      have hl := (div_le_iff₀
        (by exact_mod_cast Nat.pos_of_ne_zero hr : (0 : ℝ) < r)).mp (h r)
      simpa [logExtremal, mul_comm] using hl

/-- Bounded logarithmic rates are equivalent to existence of a literal positive
natural exponential base; the equivalence holds in every ambient universe. -/
theorem finiteGrowth_iff_exists_uniformBound {p : ℕ} (hp : 2 ≤ p) :
    FiniteGrowth p ↔ ∃ q : ℕ, 0 < q ∧ UniformSunflowerBound.{u} q p := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨q, hq⟩ := exists_nat_gt (Real.exp c)
    have hqpos : 0 < q := by
      exact_mod_cast (Real.exp_pos c).trans hq
    have hqb : ∀ r, (extremal p r : ℝ) ≤ (q : ℝ) ^ r := by
      apply (real_bound_iff_normalizedLog_le hp (by exact_mod_cast hqpos)).mpr
      intro r
      have hrc := hc (Set.mem_range_self r)
      have hlog : c ≤ Real.log q := by
        have h := Real.log_le_log (Real.exp_pos c) (le_of_lt hq)
        simpa using h
      exact hrc.trans hlog
    refine ⟨q, hqpos, (uniformBound_iff_extremal_le hp).mpr ?_⟩
    intro r
    exact_mod_cast hqb r
  · rintro ⟨q, hq, hb⟩
    have hqe := (uniformBound_iff_extremal_le hp).mp hb
    have hlog := (real_bound_iff_normalizedLog_le hp
      (show (0 : ℝ) < q by exact_mod_cast hq)).mp
      (fun r => by exact_mod_cast hqe r)
    exact ⟨Real.log q, by rintro x ⟨r, rfl⟩; exact hlog r⟩

/-- If the rate is finite, its exponential is itself a valid real base.
There is no epsilon loss or multiplicative prefactor. -/
theorem entropy_exact_real_bound {p : ℕ} (hp : 2 ≤ p) (hfin : FiniteGrowth p) :
    ∀ r, (extremal p r : ℝ) ≤ (Real.exp (entropy p)) ^ r := by
  apply (real_bound_iff_normalizedLog_le hp (Real.exp_pos _)).mpr
  simpa using normalizedLog_le_entropy hfin

theorem entropy_le_log_iff_real_bound {p : ℕ} (hp : 2 ≤ p)
    (hfin : FiniteGrowth p) {b : ℝ} (hb : 0 < b) :
    entropy p ≤ Real.log b ↔ ∀ r, (extremal p r : ℝ) ≤ b ^ r := by
  rw [entropy_le_iff hfin, real_bound_iff_normalizedLog_le hp hb]

theorem entropy_base_ge_sqrt_ten (hfin : FiniteGrowth 3) :
    Real.sqrt 10 ≤ Real.exp (entropy 3) := by
  apply eventual_real_bound_ge_sqrt_ten (Real.exp_pos _) (K := 1) (R := 0)
  intro α inst F r _ hu hf
  have h : (F.card : ℝ) ≤ extremal 3 r := by
    exact_mod_cast card_le_extremal F 3 r hu hf
  simpa using h.trans (entropy_exact_real_bound (by decide) hfin r)

/-- Fekete's lemma applied to the negative logarithms yields convergence to
the supremum of the normalized logarithms, provided that supremum is finite. -/
theorem normalizedLog_tendsto_entropy {p : ℕ} (hp : 2 ≤ p)
    (hfin : FiniteGrowth p) :
    Tendsto (normalizedLog p) atTop (𝓝 (entropy p)) := by
  let hsub := neg_logExtremal_subadditive hp
  have hbdd : BddBelow (Set.range fun r => -logExtremal p r / r) := by
    obtain ⟨c, hc⟩ := hfin
    refine ⟨-c, ?_⟩
    rintro x ⟨r, rfl⟩
    have h := hc (Set.mem_range_self r)
    change normalizedLog p r ≤ c at h
    simpa [normalizedLog, neg_div] using neg_le_neg h
  have hlim_nonneg : 0 ≤ -hsub.lim := by
    have h := hsub.lim_le_div hbdd (n := 1) (by decide)
    have hn := logExtremal_nonneg hp 1
    simp only [Nat.cast_one, div_one] at h
    linarith
  have heq : -hsub.lim = entropy p := by
    apply le_antisymm
    · have hl : -entropy p ≤ hsub.lim := by
        rw [Subadditive.lim]
        apply le_csInf (by exact ⟨_, 1, by simp, rfl⟩)
        rintro x ⟨r, _, rfl⟩
        have h := normalizedLog_le_entropy hfin r
        simpa [normalizedLog, neg_div] using neg_le_neg h
      linarith
    · apply (entropy_le_iff hfin _).mpr
      intro r
      by_cases hr : r = 0
      · simpa [hr, normalizedLog] using hlim_nonneg
      · have h := hsub.lim_le_div hbdd hr
        simpa [normalizedLog, neg_div] using neg_le_neg h
  have h := (hsub.tendsto_lim hbdd).neg
  simpa [normalizedLog, neg_div, heq] using h

/-- The root rate is the positive exponential of the normalized logarithm. -/
noncomputable def rootRate (p r : ℕ) : ℝ := Real.exp (normalizedLog p r)

theorem rootRate_pow {p : ℕ} (hp : 2 ≤ p) {r : ℕ} (hr : 0 < r) :
    (rootRate p r) ^ r = extremal p r := by
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  rw [rootRate, ← Real.exp_nat_mul]
  simp only [normalizedLog]
  rw [mul_div_cancel₀ _ hr', logExtremal,
    Real.exp_log (by exact_mod_cast extremal_pos hp r)]

theorem rootRate_tendsto {p : ℕ} (hp : 2 ≤ p) (hfin : FiniteGrowth p) :
    Tendsto (rootRate p) atTop (𝓝 (Real.exp (entropy p))) :=
  Real.continuous_exp.continuousAt.tendsto.comp (normalizedLog_tendsto_entropy hp hfin)

/-- Without assuming finite growth, any witnessed normalized rate is an
eventual strict lower bound for all normalized rates. -/
theorem eventually_normalizedLog_gt_of_witness {p : ℕ} (hp : 2 ≤ p)
    {r : ℕ} (hr : r ≠ 0) {c : ℝ} (hc : c < normalizedLog p r) :
    ∀ᶠ n in atTop, c < normalizedLog p n := by
  have h := (neg_logExtremal_subadditive hp).eventually_div_lt_of_div_lt
    hr (L := -c) (by simpa [normalizedLog, neg_div] using neg_lt_neg hc)
  simpa only [neg_div, neg_lt_neg_iff, normalizedLog] using h

/-- The classical sparse substitution witnesses and tensor products together
give a lower bound at every sufficiently large rank, not just a subsequence. -/
theorem below_sqrt_ten_eventual_extremal {b : ℝ}
    (hb : 0 < b) (hsmall : b < Real.sqrt 10) :
    ∃ R : ℕ, ∀ r, R ≤ r → b ^ r < (extremal 3 r : ℝ) := by
  obtain ⟨n, _, hn⟩ := below_sqrt_ten_iterated_counterexample (K := 1) 0 hb hsmall
  obtain ⟨α, inst, F, hu, hf, hc, _⟩ := iterated_intersecting_witness n
  have he : (10 : ℝ) ^ iterationExponent n ≤ extremal 3 (3 ^ n) := by
    have h := card_le_extremal F 3 (3 ^ n) hu hf
    rw [hc] at h
    exact_mod_cast h
  have hr : 0 < 3 ^ n := by positivity
  have hbpow : b ^ (3 ^ n) < (extremal 3 (3 ^ n) : ℝ) := by
    have hh : b ^ (3 ^ n) < (10 : ℝ) ^ iterationExponent n := by simpa using hn
    exact hh.trans_le he
  have hlog : Real.log b < normalizedLog 3 (3 ^ n) := by
    unfold normalizedLog
    apply (lt_div_iff₀ (by exact_mod_cast hr : (0 : ℝ) < (3 ^ n : ℕ))).mpr
    have h := Real.log_lt_log (pow_pos hb (3 ^ n)) hbpow
    simpa [logExtremal, Real.log_pow, mul_comm] using h
  have h := eventually_normalizedLog_gt_of_witness (by decide : 2 ≤ 3)
    (Nat.ne_of_gt hr) hlog
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    (h.and (eventually_ge_atTop (1 : ℕ)))
  refine ⟨R, ?_⟩
  intro r hrr
  obtain ⟨hl, hr⟩ := hR r hrr
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  apply (Real.log_lt_log_iff (pow_pos hb r)
    (by exact_mod_cast extremal_pos (by decide : 2 ≤ 3) r)).mp
  rw [Real.log_pow]
  have hh := (lt_div_iff₀ hr').mp hl
  simpa [logExtremal, mul_comm] using hh

/-- At every sufficiently large rank, the lower inequality has a concrete
finite representative in the canonical ground set. -/
theorem below_sqrt_ten_every_large_rank_witness {b : ℝ}
    (hb : 0 < b) (hsmall : b < Real.sqrt 10) :
    ∃ R : ℕ, ∀ r, R ≤ r →
      ∃ F : Finset (Finset (Fin (groundSize 3 r))),
        (∀ S ∈ F, S.card = r) ∧ IsSunflowerFree F 3 ∧ b ^ r < (F.card : ℝ) := by
  obtain ⟨R, hR⟩ := below_sqrt_ten_eventual_extremal hb hsmall
  refine ⟨R, ?_⟩
  intro r hr
  obtain ⟨F, hu, hf, hc⟩ := extremal_attained (by decide : 1 ≤ 3) r
  exact ⟨F, hu, hf, by simpa [hc] using hR r hr⟩

/-- Any fixed real prefactor is eventually defeated at every rank below the
classical base, with no assumption that the extremal growth rate is finite. -/
theorem below_sqrt_ten_prefactor_eventual_extremal {b : ℝ} (K : ℝ)
    (hb : 0 < b) (hsmall : b < Real.sqrt 10) :
    ∃ R : ℕ, ∀ r, R ≤ r → K * b ^ r < (extremal 3 r : ℝ) := by
  obtain ⟨c, hbc, hc⟩ := exists_between hsmall
  obtain ⟨R, hR⟩ := below_sqrt_ten_eventual_extremal (hb.trans hbc) hc
  have hratio : 1 < c / b := (lt_div_iff₀ hb).mpr (by simpa using hbc)
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt K hratio
  refine ⟨max R N, ?_⟩
  intro r hr
  have hRr : R ≤ r := (le_max_left R N).trans hr
  have hNr : N ≤ r := (le_max_right R N).trans hr
  have hpow : K < (c / b) ^ r :=
    hN.trans_le (pow_le_pow_right₀ (le_of_lt hratio) hNr)
  rw [div_pow] at hpow
  exact ((lt_div_iff₀ (pow_pos hb r)).mp hpow).trans (hR r hRr)

theorem below_sqrt_ten_prefactor_every_large_rank_witness {b : ℝ} (K : ℝ)
    (hb : 0 < b) (hsmall : b < Real.sqrt 10) :
    ∃ R : ℕ, ∀ r, R ≤ r →
      ∃ F : Finset (Finset (Fin (groundSize 3 r))),
        (∀ S ∈ F, S.card = r) ∧ IsSunflowerFree F 3 ∧
          K * b ^ r < (F.card : ℝ) := by
  obtain ⟨R, hR⟩ := below_sqrt_ten_prefactor_eventual_extremal K hb hsmall
  refine ⟨R, ?_⟩
  intro r hr
  obtain ⟨F, hu, hf, hc⟩ := extremal_attained (by decide : 1 ≤ 3) r
  exact ⟨F, hu, hf, by simpa [hc] using hR r hr⟩

/-- The opposite branch is also determined: unbounded normalized rates
diverge to positive infinity, rather than oscillating without a limit. -/
theorem normalizedLog_unbounded_tendsto_atTop {p : ℕ} (hp : 2 ≤ p)
    (hnot : ¬ FiniteGrowth p) : Tendsto (normalizedLog p) atTop atTop := by
  apply tendsto_atTop.2
  intro c
  have hex : ∃ r, c < normalizedLog p r := by
    by_contra hn
    push_neg at hn
    exact hnot ⟨c, by rintro x ⟨r, rfl⟩; exact hn r⟩
  obtain ⟨r, hr⟩ := hex
  by_cases hz : r = 0
  · have hc : c < 0 := by simpa [hz, normalizedLog] using hr
    exact Filter.Eventually.of_forall (fun n => hc.le.trans (normalizedLog_nonneg hp n))
  · exact (eventually_normalizedLog_gt_of_witness hp hz hr).mono
      (fun _ h => le_of_lt h)

theorem rootRate_unbounded_tendsto_atTop {p : ℕ} (hp : 2 ≤ p)
    (hnot : ¬ FiniteGrowth p) : Tendsto (rootRate p) atTop atTop :=
  Real.tendsto_exp_atTop.comp (normalizedLog_unbounded_tendsto_atTop hp hnot)

/-- When finite, the limiting root rate is the least possible universal
positive real exponential base, attained without a prefactor. -/
theorem entropy_base_le_iff_real_bound {p : ℕ} (hp : 2 ≤ p)
    (hfin : FiniteGrowth p) {b : ℝ} (hb : 0 < b) :
    Real.exp (entropy p) ≤ b ↔ ∀ r, (extremal p r : ℝ) ≤ b ^ r := by
  rw [← Real.exp_log hb, Real.exp_le_exp]
  simpa only [Real.log_exp] using
    entropy_le_log_iff_real_bound hp hfin (Real.exp_pos (Real.log b))

/-- The all-rank extremal root sequence always has a finite limit or diverges
to positive infinity. The open conjecture asks for the finite branch. -/
theorem rootRate_limit_dichotomy {p : ℕ} (hp : 2 ≤ p) :
    (FiniteGrowth p ∧ Tendsto (rootRate p) atTop (𝓝 (Real.exp (entropy p)))) ∨
      (¬ FiniteGrowth p ∧ Tendsto (rootRate p) atTop atTop) := by
  by_cases h : FiniteGrowth p
  · exact Or.inl ⟨h, rootRate_tendsto hp h⟩
  · exact Or.inr ⟨h, rootRate_unbounded_tendsto_atTop hp h⟩

end Erdos20GrowthRate
