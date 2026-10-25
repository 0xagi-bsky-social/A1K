import SunflowerLean.Erdos20BCWConditional

/-!
# Erdős Problem 20: conditional constant-base assembly

This module proves that the explicit open proposition `DirectSpreadMatching q p`
implies the finite extremal bound `family.card ≤ q ^ r`.  The proposition is a
theorem argument, not an axiom; this file does not claim to solve Problem 20.
-/

namespace Erdos20BCWConditional

universe u

lemma residualLink_member_disjoint_core
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {core P : Finset α}
    (hP : P ∈ residualLink family core) :
    Disjoint core P := by
  rcases mem_residualLink_iff.mp hP with ⟨S, _hSF, _hcoreS, rfl⟩
  exact Finset.disjoint_sdiff

lemma core_union_injOn_residualLink
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (core : Finset α) :
    Set.InjOn (fun P : Finset α => core ∪ P) (residualLink family core) := by
  intro P hP Q hQ hEq
  have hPd := residualLink_member_disjoint_core hP
  have hQd := residualLink_member_disjoint_core hQ
  change core ∪ P = core ∪ Q at hEq
  ext x
  constructor
  · intro hxP
    have hxUnion : x ∈ core ∪ Q := by
      rw [← hEq]
      exact Finset.mem_union_right core hxP
    rcases Finset.mem_union.mp hxUnion with hxcore | hxQ
    · exact False.elim ((Finset.disjoint_left.mp hPd) hxcore hxP)
    · exact hxQ
  · intro hxQ
    have hxUnion : x ∈ core ∪ P := by
      rw [hEq]
      exact Finset.mem_union_right core hxQ
    rcases Finset.mem_union.mp hxUnion with hxcore | hxP
    · exact False.elim ((Finset.disjoint_left.mp hQd) hxcore hxQ)
    · exact hxP

lemma residualLink_uniform
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {core : Finset α} {r : ℕ}
    (huniform : ∀ S ∈ family, S.card = r) :
    ∀ P ∈ residualLink family core, P.card = r - core.card := by
  intro P hP
  rcases mem_residualLink_iff.mp hP with ⟨S, hSF, hcoreS, rfl⟩
  rw [Finset.card_sdiff_of_subset hcoreS, huniform S hSF]

lemma core_union_residual_mem_family
    {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {core P : Finset α}
    (hP : P ∈ residualLink family core) :
    core ∪ P ∈ family := by
  rcases mem_residualLink_iff.mp hP with ⟨S, hSF, hcoreS, rfl⟩
  simpa [Finset.union_sdiff_of_subset hcoreS] using hSF

lemma core_union_inter_eq_core
    {α : Type*} [DecidableEq α]
    {core P Q : Finset α}
    (hPQ : P ∩ Q = ∅) :
    (core ∪ P) ∩ (core ∪ Q) = core := by
  ext x
  constructor
  · intro hx
    have hx' := Finset.mem_inter.mp hx
    rcases Finset.mem_union.mp hx'.1 with hxcore | hxP
    · exact hxcore
    · rcases Finset.mem_union.mp hx'.2 with hxcore | hxQ
      · exact hxcore
      · have hxPQ : x ∈ P ∩ Q := Finset.mem_inter.mpr ⟨hxP, hxQ⟩
        rw [hPQ] at hxPQ
        simp at hxPQ
  · intro hxcore
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_union_left P hxcore, Finset.mem_union_left Q hxcore⟩

theorem residual_matching_lifts_sunflower
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (core : Finset α)
    (matching : Finset (Finset α)) (p : ℕ)
    (hsub : matching ⊆ residualLink family core)
    (hcard : matching.card = p)
    (hdis : IsPairwiseDisjoint matching) :
    ∃ lifted : Finset (Finset α),
      lifted ⊆ family ∧ IsSunflower lifted p := by
  let lifted := matching.image (fun P => core ∪ P)
  refine ⟨lifted, ?_, ?_⟩
  · intro S hS
    rcases Finset.mem_image.mp hS with ⟨P, hP, rfl⟩
    exact core_union_residual_mem_family (hsub hP)
  · refine ⟨?_, core, ?_⟩
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
      exact core_union_inter_eq_core
        (hdis P Q hP hQ hPQ)

theorem card_le_pow_of_directSpreadMatching
    {α : Type u} [DecidableEq α]
    (family : Finset (Finset α)) (r p q : ℕ)
    (huniform : ∀ S ∈ family, S.card = r)
    (hfree : IsSunflowerFree family p)
    (hq : 0 < q)
    (hdirect : DirectSpreadMatching.{u} q p) :
    family.card ≤ q ^ r := by
  classical
  by_cases hempty : family = ∅
  · simp [hempty]
  have hfamily : family.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨core, hcore, hmax⟩ := exists_maximal_dense_core family q
  have hspread : IsRSpread (residualLink family core) q :=
    maximal_dense_core_residual_isSpread family q hfamily hq core hcore hmax
  have hresBound : (residualLink family core).card ≤ q ^ (r - core.card) := by
    by_contra hnot
    have hlarge : q ^ (r - core.card) < (residualLink family core).card :=
      Nat.lt_of_not_ge hnot
    obtain ⟨matching, hsub, hcard, hdis⟩ :=
      hdirect (α := α) (residualLink family core) (r - core.card)
        (residualLink_uniform huniform) hspread hlarge
    obtain ⟨lifted, hliftSub, hliftSun⟩ :=
      residual_matching_lifts_sunflower family core matching p hsub hcard hdis
    exact (hfree lifted hliftSub) hliftSun
  have hdense : IsDenseCore family q core := (Finset.mem_filter.mp hcore).2
  have hcoreLe : core.card ≤ r := by
    obtain ⟨P, hP⟩ := hspread.2.1
    rcases mem_residualLink_iff.mp hP with ⟨S, hSF, hcoreS, _hSP⟩
    rw [← huniform S hSF]
    exact Finset.card_le_card hcoreS
  calc
    family.card ≤ (upperStar family core).card * q ^ core.card := hdense
    _ = (residualLink family core).card * q ^ core.card := by
      rw [card_residualLink]
    _ ≤ q ^ (r - core.card) * q ^ core.card :=
      Nat.mul_le_mul_right _ hresBound
    _ = q ^ r := by
      rw [← pow_add, Nat.sub_add_cancel hcoreLe]

#print axioms residual_matching_lifts_sunflower
#print axioms card_le_pow_of_directSpreadMatching

end Erdos20BCWConditional
