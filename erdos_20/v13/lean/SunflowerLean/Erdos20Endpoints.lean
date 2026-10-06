import SunflowerLean.Erdos20BCWBridge

/-! Exact forcing endpoints for the inherited extremal convention. -/
namespace Erdos20Endpoints

universe u

/-- The universal extremal bound; the base is chosen before the rank. -/
def UniformExtremalBound (q p : ℕ) : Prop :=
  ∀ {α : Type u} [DecidableEq α] (family : Finset (Finset α)) (r : ℕ),
    (∀ S ∈ family, S.card = r) → IsSunflowerFree family p →
    family.card ≤ q ^ r

/-- Cardinality at least `N` forces a sunflower in every rank-`r` family. -/
def Forces (r p N : ℕ) : Prop :=
  ∀ {α : Type u} [DecidableEq α] (family : Finset (Finset α)),
    (∀ S ∈ family, S.card = r) → N ≤ family.card →
    ∃ subfamily, subfamily ⊆ family ∧ IsSunflower subfamily p

theorem forces_succ_pow_iff (q p : ℕ) :
    (∀ r, Forces.{u} r p (q ^ r + 1)) ↔ UniformExtremalBound.{u} q p := by
  constructor
  · intro h α _ family r huniform hfree
    by_contra hnot
    obtain ⟨subfamily, hsub, hsun⟩ :=
      h r family huniform (by omega)
    exact hfree subfamily hsub hsun
  · intro h r α _ family huniform hlarge
    by_contra hnot
    have hfree : IsSunflowerFree family p := by
      intro subfamily hsub hsun
      exact hnot ⟨subfamily, hsub, hsun⟩
    have hbound := h family r huniform hfree
    omega

theorem pow_add_one_lt_pow_add_two (q r : ℕ) (hr : 0 < r) :
    q ^ r + 1 < (q + 2) ^ r := by
  have h1 : q ^ r < (q + 1) ^ r :=
    Nat.pow_lt_pow_left (by omega) (by omega)
  have h2 : (q + 1) ^ r < (q + 2) ^ r :=
    Nat.pow_lt_pow_left (by omega) (by omega)
  omega

/-- Website-style strict exponential forcing threshold, without taking an
undefined maximum or least natural number. -/
theorem strict_forcing_threshold_of_extremal (q p r : ℕ) (hr : 0 < r)
    (hbound : UniformExtremalBound.{u} q p) :
    ∃ N, Forces.{u} r p N ∧ N < (q + 2) ^ r := by
  exact ⟨q ^ r + 1, (forces_succ_pow_iff q p).mpr hbound r,
    pow_add_one_lt_pow_add_two q r hr⟩

theorem strict_forcing_threshold_of_direct (q p r : ℕ) (hq : 0 < q)
    (hr : 0 < r)
    (hdirect : Erdos20BCWConditional.DirectSpreadMatching.{u} q p) :
    ∃ N, Forces.{u} r p N ∧ N < (q + 2) ^ r := by
  apply strict_forcing_threshold_of_extremal q p r hr
  intro α _ family rank huniform hfree
  exact Erdos20BCWConditional.card_le_pow_of_directSpreadMatching
    family rank p q huniform hfree hq hdirect

/-- Literal-statement fidelity for the extremal interface. -/
theorem uniformExtremalBound_expanded (q p : ℕ) :
    UniformExtremalBound.{u} q p ↔
      ∀ {α : Type u} [DecidableEq α] (family : Finset (Finset α)) (r : ℕ),
      (∀ S ∈ family, S.card = r) →
      (∀ subfamily : Finset (Finset α), subfamily ⊆ family →
        ¬ (subfamily.card = p ∧ ∃ core : Finset α,
          ∀ S T : Finset α, S ∈ subfamily → T ∈ subfamily →
            S ≠ T → S ∩ T = core)) → family.card ≤ q ^ r := Iff.rfl

end Erdos20Endpoints

#print axioms Erdos20Endpoints.forces_succ_pow_iff
#print axioms Erdos20Endpoints.pow_add_one_lt_pow_add_two
#print axioms Erdos20Endpoints.strict_forcing_threshold_of_extremal
#print axioms Erdos20Endpoints.strict_forcing_threshold_of_direct
#print axioms Erdos20Endpoints.uniformExtremalBound_expanded
