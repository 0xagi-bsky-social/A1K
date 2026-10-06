import SunflowerLean.Erdos20BCWBridge

/-!
# Strict spread in maximal dense-core links

The maximality used in the prior dense-core decomposition gives strict link
inequalities for every nonempty set, including the full residual member.
The matching interface below remains a hypothesis, not a proved conjecture.
-/

namespace Erdos20StrictCore

open Erdos20BCWConditional

universe u

/-- Strict normalized spread at every nonempty set, with the usual positive
scale and nonempty family conventions. -/
def IsStrictRSpread {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (q : ℕ) : Prop :=
  0 < q ∧ family.Nonempty ∧
    ∀ extra : Finset α, extra.Nonempty →
      (family.filter (fun P => extra ⊆ P)).card * q ^ extra.card < family.card

lemma strictSpread_implies_spread
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {q : ℕ}
    (hstrict : IsStrictRSpread family q) : IsRSpread family q := by
  refine ⟨hstrict.1, hstrict.2.1, ?_⟩
  intro extra
  by_cases he : extra.Nonempty
  · exact Nat.le_of_lt (hstrict.2.2 extra he)
  · rw [Finset.not_nonempty_iff_eq_empty] at he
    subst extra
    simp

/-- Maximality rules out equality as well as a strict spread violation. -/
theorem maximal_dense_core_residual_isStrictSpread
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (q : ℕ)
    (hfamily : family.Nonempty) (hq : 0 < q)
    (core : Finset α)
    (hcore : core ∈ denseCores family q)
    (hmax : ∀ other ∈ denseCores family q, other.card ≤ core.card) :
    IsStrictRSpread (residualLink family core) q := by
  classical
  have hspread := maximal_dense_core_residual_isSpread family q hfamily hq core hcore hmax
  have hdense : IsDenseCore family q core := (Finset.mem_filter.mp hcore).2
  refine ⟨hq, hspread.2.1, ?_⟩
  intro extra hextra
  by_contra hnot
  have hviol : (residualLink family core).card ≤
      ((residualLink family core).filter (fun P => extra ⊆ P)).card *
        q ^ extra.card := Nat.le_of_not_gt hnot
  have hfiltered :
      ((residualLink family core).filter (fun P => extra ⊆ P)).Nonempty := by
    apply Finset.card_pos.mp
    by_contra h
    have hz : ((residualLink family core).filter
        (fun P => extra ⊆ P)).card = 0 := Nat.eq_zero_of_not_pos h
    have hrespos := hspread.2.1.card_pos
    simp only [hz, zero_mul] at hviol
    omega
  rcases hfiltered with ⟨P, hP⟩
  have hP' := Finset.mem_filter.mp hP
  rcases mem_residualLink_iff.mp hP'.1 with ⟨S, hSF, hcoreS, hSP⟩
  have hdis : Disjoint core extra := by
    rw [Finset.disjoint_left]
    intro x hxcore hxextra
    have hxP : x ∈ P := hP'.2 hxextra
    rw [← hSP] at hxP
    exact (Finset.mem_sdiff.mp hxP).2 hxcore
  have hlocal : (upperStar family core).card ≤
      (upperStar family (core ∪ extra)).card * q ^ extra.card := by
    simpa [card_residualLink,
      card_filter_residualLink family core extra hdis] using hviol
  have hcard_union : (core ∪ extra).card = core.card + extra.card :=
    Finset.card_union_of_disjoint hdis
  have hotherDense : IsDenseCore family q (core ∪ extra) := by
    unfold IsDenseCore
    calc
      family.card ≤ (upperStar family core).card * q ^ core.card := hdense
      _ ≤ ((upperStar family (core ∪ extra)).card * q ^ extra.card) *
          q ^ core.card := Nat.mul_le_mul_right _ hlocal
      _ = (upperStar family (core ∪ extra)).card *
          q ^ (core ∪ extra).card := by
        rw [hcard_union, pow_add]
        ac_rfl
  have hotherCandidate : core ∪ extra ∈ coreCandidates family := by
    apply Finset.mem_powerset.mpr
    apply Finset.union_subset
    · exact Finset.Subset.trans hcoreS (member_subset_support hSF)
    · intro x hx
      have hxP := hP'.2 hx
      rw [← hSP] at hxP
      exact member_subset_support hSF (Finset.mem_sdiff.mp hxP).1
  have hother : core ∪ extra ∈ denseCores family q :=
    Finset.mem_filter.mpr ⟨hotherCandidate, hotherDense⟩
  have hle := hmax (core ∪ extra) hother
  rw [hcard_union] at hle
  have hextra_card := hextra.card_pos
  omega

/-- The prior interface's strict cardinality endpoint is automatic for a
strictly spread family of positive uniform rank. -/
theorem strictSpread_card_gt_pow
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (q m : ℕ)
    (huniform : ∀ P ∈ family, P.card = m)
    (hm : 0 < m) (hstrict : IsStrictRSpread family q) :
    q ^ m < family.card := by
  classical
  obtain ⟨P, hP⟩ := hstrict.2.1
  have hPnonempty : P.Nonempty := Finset.card_pos.mp (by simpa [huniform P hP] using hm)
  have hfilter : family.filter (fun Q => P ⊆ Q) = {P} := by
    ext Q
    constructor
    · intro hQ
      have hQ' := Finset.mem_filter.mp hQ
      have heq : P = Q := Finset.eq_of_subset_of_card_le hQ'.2
        (by rw [huniform P hP, huniform Q hQ'.1])
      simpa using heq.symm
    · intro hQ
      have heq : Q = P := Finset.mem_singleton.mp hQ
      subst Q
      exact Finset.mem_filter.mpr ⟨hP, Finset.Subset.refl P⟩
  simpa [hfilter, huniform P hP] using hstrict.2.2 P hPnonempty

/-- A weaker sufficient matching premise, restricted to positive-rank families
with strict normalized spread. No theorem here proves this proposition. -/
def StrictSpreadMatching (q p : ℕ) : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (petals : Finset (Finset α)) (m : ℕ),
    (∀ P ∈ petals, P.card = m) →
    0 < m → IsStrictRSpread petals q →
    ∃ matching : Finset (Finset α),
      matching ⊆ petals ∧ matching.card = p ∧ IsPairwiseDisjoint matching

theorem directSpreadMatching_implies_strictSpreadMatching
    {q p : ℕ} (hdirect : DirectSpreadMatching.{u} q p) :
    StrictSpreadMatching.{u} q p := by
  intro α _ petals m huniform hm hstrict
  exact hdirect petals m huniform (strictSpread_implies_spread hstrict)
    (strictSpread_card_gt_pow petals q m huniform hm hstrict)

/-- The stronger residual invariant suffices for the same extremal conclusion,
using only the restricted strict-spread matching hypothesis. -/
theorem card_le_pow_of_strictSpreadMatching
    {α : Type u} [DecidableEq α]
    (family : Finset (Finset α)) (r p q : ℕ)
    (huniform : ∀ S ∈ family, S.card = r)
    (hfree : IsSunflowerFree family p)
    (hq : 0 < q)
    (hmatching : StrictSpreadMatching.{u} q p) :
    family.card ≤ q ^ r := by
  classical
  by_contra hnot
  have hlarge : q ^ r < family.card := Nat.lt_of_not_ge hnot
  have hfamily : family.Nonempty := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hlarge)
  obtain ⟨core, hcore, hmax⟩ := exists_maximal_dense_core family q
  have hstrict := maximal_dense_core_residual_isStrictSpread
    family q hfamily hq core hcore hmax
  have hresUniform := residualLink_uniform huniform (core := core)
  have hdense : IsDenseCore family q core := (Finset.mem_filter.mp hcore).2
  have hcoreLe : core.card ≤ r := by
    obtain ⟨P, hP⟩ := hstrict.2.1
    rcases mem_residualLink_iff.mp hP with ⟨S, hSF, hcoreS, _⟩
    rw [← huniform S hSF]
    exact Finset.card_le_card hcoreS
  have hm : 0 < r - core.card := by
    by_contra hnotpos
    have hzero : r - core.card = 0 := by omega
    have hcoreEq : core.card = r := by omega
    have hsub : residualLink family core ⊆ ({∅} : Finset (Finset α)) := by
      intro P hP
      have hc : P.card = 0 := by simpa [hzero] using hresUniform P hP
      simpa [Finset.card_eq_zero.mp hc]
    have hresBound : (residualLink family core).card ≤ 1 := by
      simpa using Finset.card_le_card hsub
    have hbound : family.card ≤ q ^ r := by
      calc
        family.card ≤ (upperStar family core).card * q ^ core.card := hdense
        _ = (residualLink family core).card * q ^ r := by
          rw [card_residualLink, hcoreEq]
        _ ≤ 1 * q ^ r := Nat.mul_le_mul_right _ hresBound
        _ = q ^ r := one_mul _
    omega
  obtain ⟨matching, hsub, hcard, hdis⟩ :=
    hmatching (residualLink family core) (r - core.card) hresUniform hm hstrict
  obtain ⟨lifted, hliftSub, hliftSun⟩ :=
    residual_matching_lifts_sunflower family core matching p hsub hcard hdis
  exact (hfree lifted hliftSub) hliftSun

/-- Adding back the deleted core lifts an arbitrary sunflower, not only a
pairwise-disjoint matching. The lifted core is the union of both cores. -/
theorem residual_sunflower_lifts
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (core : Finset α)
    (sunflower : Finset (Finset α)) (p : ℕ)
    (hsub : sunflower ⊆ residualLink family core)
    (hsun : IsSunflower sunflower p) :
    ∃ lifted : Finset (Finset α), lifted ⊆ family ∧ IsSunflower lifted p := by
  classical
  rcases hsun with ⟨hcard, inner, hinter⟩
  refine ⟨sunflower.image (fun P => core ∪ P), ?_, ?_⟩
  · intro S hS
    rcases Finset.mem_image.mp hS with ⟨P, hP, rfl⟩
    exact core_union_residual_mem_family (hsub hP)
  · refine ⟨?_, core ∪ inner, ?_⟩
    · rw [Finset.card_image_of_injOn]
      · exact hcard
      · exact (core_union_injOn_residualLink family core).mono hsub
    · intro S T hS hT hne
      rcases Finset.mem_image.mp hS with ⟨P, hP, rfl⟩
      rcases Finset.mem_image.mp hT with ⟨Q, hQ, rfl⟩
      have hPQ : P ≠ Q := by
        intro h
        subst Q
        exact hne rfl
      rw [← Finset.union_inter_distrib_left, hinter P Q hP hQ hPQ]

/-- Residual links preserve sunflower-freeness even when the residual sunflower
has a nonempty core. -/
theorem residualLink_sunflowerFree
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {core : Finset α} {p : ℕ}
    (hfree : IsSunflowerFree family p) :
    IsSunflowerFree (residualLink family core) p := by
  intro sunflower hsub hsun
  obtain ⟨lifted, hmem, hlift⟩ := residual_sunflower_lifts family core sunflower p hsub hsun
  exact hfree lifted hmem hlift

/-- Exact universal extremal statement in the same finite-set model. -/
def UniformSunflowerBound (q p : ℕ) : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r : ℕ),
    (∀ S ∈ family, S.card = r) → IsSunflowerFree family p →
    family.card ≤ q ^ r

/-- Restricted sunflower existence interface. The sunflower is allowed to have
an arbitrary core; this proposition is still unproved for constant scale. -/
def StrictSpreadSunflower (q p : ℕ) : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r : ℕ),
    (∀ S ∈ family, S.card = r) → 0 < r → IsStrictRSpread family q →
    ∃ sunflower : Finset (Finset α), sunflower ⊆ family ∧ IsSunflower sunflower p

theorem strictSpreadMatching_implies_strictSpreadSunflower
    {q p : ℕ} (hmatching : StrictSpreadMatching.{u} q p) :
    StrictSpreadSunflower.{u} q p := by
  intro α _ family r huniform hr hstrict
  obtain ⟨matching, hsub, hcard, hdis⟩ := hmatching family r huniform hr hstrict
  exact ⟨matching, hsub, disjoint_is_sunflower matching p hcard hdis⟩

/-- A family exceeding q^r leaves a positive-rank maximal dense-core residual. -/
theorem maximal_dense_core_residual_rank_pos
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r q : ℕ)
    (huniform : ∀ S ∈ family, S.card = r)
    (hlarge : q ^ r < family.card) (hq : 0 < q)
    (core : Finset α)
    (hcore : core ∈ denseCores family q)
    (hmax : ∀ other ∈ denseCores family q, other.card ≤ core.card) :
    0 < r - core.card := by
  classical
  have hfamily : family.Nonempty := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hlarge)
  have hstrict := maximal_dense_core_residual_isStrictSpread
    family q hfamily hq core hcore hmax
  have hresUniform := residualLink_uniform huniform (core := core)
  have hdense : IsDenseCore family q core := (Finset.mem_filter.mp hcore).2
  have hcoreLe : core.card ≤ r := by
    obtain ⟨P, hP⟩ := hstrict.2.1
    rcases mem_residualLink_iff.mp hP with ⟨S, hSF, hcoreS, _⟩
    rw [← huniform S hSF]
    exact Finset.card_le_card hcoreS
  by_contra hnotpos
  have hzero : r - core.card = 0 := by omega
  have hcoreEq : core.card = r := by omega
  have hsub : residualLink family core ⊆ ({∅} : Finset (Finset α)) := by
    intro P hP
    have hc : P.card = 0 := by simpa [hzero] using hresUniform P hP
    simpa [Finset.card_eq_zero.mp hc]
  have hresBound : (residualLink family core).card ≤ 1 := by
    simpa using Finset.card_le_card hsub
  have hbound : family.card ≤ q ^ r := by
    calc
      family.card ≤ (upperStar family core).card * q ^ core.card := hdense
      _ = (residualLink family core).card * q ^ r := by rw [card_residualLink, hcoreEq]
      _ ≤ 1 * q ^ r := Nat.mul_le_mul_right _ hresBound
      _ = q ^ r := one_mul _
  omega

/-- Forward direction of the exact same-base reduction. -/
theorem uniformBound_of_strictSpreadSunflower
    {q p : ℕ} (hq : 0 < q) (hstrictSun : StrictSpreadSunflower.{u} q p) :
    UniformSunflowerBound.{u} q p := by
  intro α _ family r huniform hfree
  classical
  by_contra hnot
  have hlarge : q ^ r < family.card := Nat.lt_of_not_ge hnot
  have hfamily : family.Nonempty := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hlarge)
  obtain ⟨core, hcore, hmax⟩ := exists_maximal_dense_core family q
  have hstrict := maximal_dense_core_residual_isStrictSpread family q hfamily hq core hcore hmax
  have hm := maximal_dense_core_residual_rank_pos family r q huniform hlarge hq core hcore hmax
  obtain ⟨sunflower, hsub, hsun⟩ := hstrictSun (residualLink family core) (r - core.card)
    (residualLink_uniform huniform) hm hstrict
  exact residualLink_sunflowerFree hfree sunflower hsub hsun

/-- Reverse direction uses the automatic strict density surplus. -/
theorem strictSpreadSunflower_of_uniformBound
    {q p : ℕ} (hbound : UniformSunflowerBound.{u} q p) :
    StrictSpreadSunflower.{u} q p := by
  intro α _ family r huniform hr hstrict
  classical
  by_contra hnot
  have hfree : IsSunflowerFree family p := by
    intro sunflower hsub hsun
    exact hnot ⟨sunflower, hsub, hsun⟩
  have hle := hbound family r huniform hfree
  have hlt := strictSpread_card_gt_pow family q r huniform hr hstrict
  omega

/-- An equivalence of two still-open fixed-base propositions. It does not
establish either proposition for a rank-independent base. -/
theorem strictSpreadSunflower_iff_uniformBound
    {q p : ℕ} (hq : 0 < q) :
    StrictSpreadSunflower.{u} q p ↔ UniformSunflowerBound.{u} q p :=
  ⟨uniformBound_of_strictSpreadSunflower hq, strictSpreadSunflower_of_uniformBound⟩

#print axioms residual_sunflower_lifts
#print axioms residualLink_sunflowerFree
#print axioms strictSpreadMatching_implies_strictSpreadSunflower
#print axioms maximal_dense_core_residual_rank_pos
#print axioms uniformBound_of_strictSpreadSunflower
#print axioms strictSpreadSunflower_of_uniformBound
#print axioms strictSpreadSunflower_iff_uniformBound

#print axioms strictSpread_implies_spread
#print axioms maximal_dense_core_residual_isStrictSpread
#print axioms strictSpread_card_gt_pow
#print axioms directSpreadMatching_implies_strictSpreadMatching
#print axioms card_le_pow_of_strictSpreadMatching

end Erdos20StrictCore
