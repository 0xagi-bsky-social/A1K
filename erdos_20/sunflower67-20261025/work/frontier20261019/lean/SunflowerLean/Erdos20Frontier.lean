import SunflowerLean.Erdos20StrictCore
import SunflowerLean.Erdos20SpreadPacking
import SunflowerLean.Erdos20Obstructions

/-! Public statement, exact bridge, and boundary tests for the new frontier. -/
namespace Erdos20Frontier

open Erdos20StrictCore Erdos20Endpoints Erdos20BCWConditional

universe u

def SunflowerConjecture : Prop :=
  ∀ p : ℕ, 3 ≤ p → ∃ q : ℕ, 0 < q ∧ UniformExtremalBound.{u} q p

def StrictSpreadConjecture : Prop :=
  ∀ p : ℕ, 3 ≤ p → ∃ q : ℕ, 0 < q ∧ StrictSpreadSunflower.{u} q p

theorem uniformBound_interfaces_agree (q p : ℕ) :
    UniformSunflowerBound.{u} q p ↔ UniformExtremalBound.{u} q p := Iff.rfl

theorem sunflowerConjecture_iff_strictSpreadConjecture :
    SunflowerConjecture.{u} ↔ StrictSpreadConjecture.{u} := by
  constructor
  · intro h p hp
    obtain ⟨q, hq, hb⟩ := h p hp
    exact ⟨q, hq, strictSpreadSunflower_of_uniformBound hb⟩
  · intro h p hp
    obtain ⟨q, hq, hs⟩ := h p hp
    exact ⟨q, hq, uniformBound_of_strictSpreadSunflower hq hs⟩

theorem forcing_of_strictSpreadSunflower (q p r : ℕ) (hq : 0 < q)
    (hr : 0 < r) (hs : StrictSpreadSunflower.{u} q p) :
    ∃ N, Forces.{u} r p N ∧ N < (q + 2) ^ r :=
  strict_forcing_threshold_of_extremal q p r hr
    (uniformBound_of_strictSpreadSunflower hq hs)

theorem strictSpreadSunflower_expanded (q p : ℕ) :
    StrictSpreadSunflower.{u} q p ↔
      ∀ {α : Type u} [DecidableEq α]
        (family : Finset (Finset α)) (r : ℕ),
      (∀ S ∈ family, S.card = r) → 0 < r →
      (0 < q ∧ family.Nonempty ∧ ∀ T : Finset α, T.Nonempty →
        (family.filter (fun S => T ⊆ S)).card * q ^ T.card < family.card) →
      ∃ sunflower : Finset (Finset α), sunflower ⊆ family ∧
        sunflower.card = p ∧ ∃ core : Finset α,
          ∀ S T : Finset α, S ∈ sunflower → T ∈ sunflower →
            S ≠ T → S ∩ T = core := Iff.rfl

/-- The positive-rank condition cannot be silently removed. -/
theorem rank_zero_exception (q : ℕ) (hq : 0 < q) :
    IsStrictRSpread ({∅} : Finset (Finset (Fin 1))) q ∧
      ({∅} : Finset (Finset (Fin 1))).card = q ^ 0 ∧
      ¬ ∃ sunflower : Finset (Finset (Fin 1)),
        sunflower ⊆ {∅} ∧ IsSunflower sunflower 2 := by
  refine ⟨⟨hq, by simp, ?_⟩, by simp, ?_⟩
  · intro extra he
    have hnot : ¬ extra ⊆ (∅ : Finset (Fin 1)) := by
      intro h
      have hz := Finset.subset_empty.mp h
      simp [hz] at he
    simp [hnot]
  · rintro ⟨sunflower, hsub, hsun⟩
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    rw [hsun.1] at hc
    omega

theorem strictSpread_free_rank_lower_bound
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r q p : ℕ)
    (hr : 0 < r) (huniform : ∀ S ∈ family, S.card = r)
    (hstrict : IsStrictRSpread family q) (hfree : IsSunflowerFree family p) :
    q < r * (p - 1) := by
  by_contra hh
  have hthreshold : r * (p - 1) ≤ q := Nat.le_of_not_gt hh
  obtain ⟨matching, hsub, hcard, hdis⟩ :=
    Erdos20SpreadPacking.matching_of_strictSpread_low_rank
      family r q p hr huniform hstrict hthreshold
  exact hfree matching hsub (disjoint_is_sunflower matching p hcard hdis)

/-- Every counterexample to a fixed-base bound produces a strict-spread
sunflower-free residual whose rank is beyond the elementary packing range. -/
theorem counterexample_has_high_rank_strict_residual
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r q p : ℕ)
    (hq : 0 < q) (huniform : ∀ S ∈ family, S.card = r)
    (hfree : IsSunflowerFree family p) (hlarge : q ^ r < family.card) :
    ∃ core : Finset α,
      IsStrictRSpread (residualLink family core) q ∧
      IsSunflowerFree (residualLink family core) p ∧
      0 < r - core.card ∧ q < (r - core.card) * (p - 1) := by
  have hne : family.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨core, hcore, hmax⟩ := exists_maximal_dense_core family q
  have hs := maximal_dense_core_residual_isStrictSpread family q hne hq core hcore hmax
  have hr := maximal_dense_core_residual_rank_pos family r q huniform hlarge hq
    core hcore hmax
  have hf : IsSunflowerFree (residualLink family core) p := residualLink_sunflowerFree hfree
  exact ⟨core, hs, hf, hr, strictSpread_free_rank_lower_bound
    (residualLink family core) (r - core.card) q p hr (residualLink_uniform huniform) hs hf⟩

theorem cycleFive_not_strictSpreadSunflower :
    ¬ StrictSpreadSunflower.{0} 2 3 := by
  intro hs
  exact Erdos20Obstructions.not_uniformExtremalBound_two_three
    (uniformBound_of_strictSpreadSunflower (by decide) hs)

end Erdos20Frontier

#print axioms Erdos20Frontier.sunflowerConjecture_iff_strictSpreadConjecture
#print axioms Erdos20Frontier.forcing_of_strictSpreadSunflower
#print axioms Erdos20Frontier.strictSpreadSunflower_expanded
#print axioms Erdos20Frontier.rank_zero_exception
#print axioms Erdos20Frontier.strictSpread_free_rank_lower_bound
#print axioms Erdos20Frontier.counterexample_has_high_rank_strict_residual
#print axioms Erdos20Frontier.cycleFive_not_strictSpreadSunflower
