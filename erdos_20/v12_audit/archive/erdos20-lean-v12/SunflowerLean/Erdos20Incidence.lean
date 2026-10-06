import SunflowerLean.Erdos20Critical

/-! A refined matching-cover recurrence.  The matching members themselves
contribute repeated incidences, which the union bound discards. -/
namespace Erdos20Incidence

open Erdos20BCWConditional Erdos20StrictCore Erdos20Classical

/-- Double-count incidences with an arbitrary finite set. -/
theorem incidence_sum_eq {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (cover : Finset α) :
    (∑ S ∈ family, (S ∩ cover).card) =
      ∑ x ∈ cover, (family.filter (fun S => x ∈ S)).card := by
  classical
  have hf (S : Finset α) : S ∩ cover = cover.filter (fun x => x ∈ S) := by
    ext x
    simp [and_comm]
  calc
    _ = ∑ S ∈ family, ∑ x ∈ cover, if x ∈ S then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      rw [hf]
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Every selected covered member contributes its full rank, while each
other member contributes at least one incidence. No disjointness is needed. -/
theorem incidence_defect_lower_bound {α : Type*} [DecidableEq α]
    (family selected : Finset (Finset α)) (cover : Finset α) (r : ℕ)
    (hsub : selected ⊆ family)
    (huniform : ∀ S ∈ selected, S.card = r)
    (hcontained : ∀ S ∈ selected, S ⊆ cover)
    (hhits : ∀ S ∈ family, (S ∩ cover).Nonempty) :
    family.card + selected.card * (r - 1) ≤
      ∑ x ∈ cover, (family.filter (fun S => x ∈ S)).card := by
  classical
  rw [← incidence_sum_eq]
  have hsel : (∑ S ∈ selected, (S ∩ cover).card) = selected.card * r := by
    calc
      _ = ∑ _S ∈ selected, r := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [Finset.inter_eq_left.mpr (hcontained S hS), huniform S hS]
      _ = _ := by simp
  have hrest : (family \ selected).card ≤
      ∑ S ∈ family \ selected, (S ∩ cover).card := by
    calc
      _ = ∑ _S ∈ family \ selected, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun S hS => (hhits S (Finset.mem_sdiff.mp hS).1).card_pos)
  have hsplit := Finset.sum_sdiff hsub (f := fun S => (S ∩ cover).card)
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  by_cases hr : r = 0
  · subst r
    have he : selected = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      have hs := huniform S hS
      have hh := (hhits S (hsub hS)).card_pos
      have hi := Finset.card_le_card (Finset.inter_subset_left (s₁ := S) (s₂ := cover))
      omega
    simp [he] at hrest ⊢
    exact hrest
  · have hr1 : r - 1 + 1 = r := by omega
    rw [hsel] at hsplit
    nlinarith

/-- A sunflower-free family has a matching-cover with a certified incidence
deficit. This strengthens the elementary matching-cover union bound. -/
theorem exists_matching_incidence_bound {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r p B : ℕ)
    (hr : 0 < r) (huniform : ∀ S ∈ family, S.card = r)
    (hfree : IsSunflowerFree family p)
    (hdegree : ∀ x, (family.filter (fun S => x ∈ S)).card ≤ B) :
    ∃ t : ℕ, t ≤ p - 1 ∧ family.card + t * (r - 1) ≤ r * t * B := by
  classical
  obtain ⟨M, hsub, hdis, hhit⟩ := exists_pairwiseDisjoint_hitting_subfamily family
    (fun S hS => Finset.card_pos.mp (by rw [huniform S hS]; exact hr))
  have ht := pairwiseDisjoint_card_lt_forbidden family M p hsub hdis hfree
  refine ⟨M.card, by omega, ?_⟩
  have hlo := incidence_defect_lower_bound family M (M.biUnion id) r hsub
    (fun S hS => huniform S (hsub hS))
    (fun S hS x hx => Finset.mem_biUnion.mpr ⟨S, hS, hx⟩) hhit
  have hc : (M.biUnion id).card ≤ r * M.card := by
    simpa [Nat.mul_comm] using Finset.card_biUnion_le_card_mul M id r
      (fun S hS => le_of_eq (huniform S (hsub hS)))
  calc
    _ ≤ ∑ x ∈ M.biUnion id, (family.filter (fun S => x ∈ S)).card := hlo
    _ ≤ ∑ _x ∈ M.biUnion id, B := Finset.sum_le_sum (fun x _ => hdegree x)
    _ = (M.biUnion id).card * B := by simp
    _ ≤ r * M.card * B := Nat.mul_le_mul_right B hc

/-- A degree ceiling gives the sharpened one-step recurrence. -/
theorem card_le_refined_step {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r p B : ℕ)
    (hr : 0 < r) (hB : 0 < B)
    (huniform : ∀ S ∈ family, S.card = r)
    (hfree : IsSunflowerFree family p)
    (hdegree : ∀ x, (family.filter (fun S => x ∈ S)).card ≤ B) :
    family.card ≤ (p - 1) * (r * B - (r - 1)) := by
  obtain ⟨t, ht, hb⟩ := exists_matching_incidence_bound family r p B hr huniform hfree hdegree
  have hs : r - 1 ≤ r * B := by
    apply (Nat.sub_le r 1).trans
    simpa using Nat.mul_le_mul_left r (show 1 ≤ B by omega)
  have he := Nat.sub_add_cancel hs
  have hsmall : family.card ≤ t * (r * B - (r - 1)) := by nlinarith
  exact hsmall.trans (Nat.mul_le_mul_right _ ht)

/-- An explicit elementary refinement of the classical factorial recurrence. -/
def refinedBound (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | r + 1 => (p - 1) * ((r + 1) * refinedBound p r - r)

theorem refinedBound_pos {p : ℕ} (hp : 2 ≤ p) (r : ℕ) :
    0 < refinedBound p r := by
  induction r with
  | zero => simp [refinedBound]
  | succ r ih =>
    simp only [refinedBound]
    have : r < (r + 1) * refinedBound p r := by nlinarith
    exact Nat.mul_pos (by omega) (Nat.sub_pos_of_lt this)

/-- The refined recurrence bounds every uniform sunflower-free family. -/
theorem refined_sunflower_bound {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r p : ℕ) (hp : 2 ≤ p)
    (huniform : ∀ S ∈ family, S.card = r)
    (hfree : IsSunflowerFree family p) :
    family.card ≤ refinedBound p r := by
  induction r generalizing family with
  | zero =>
    have hsub : family ⊆ ({∅} : Finset (Finset α)) := by
      intro S hS
      simp [Finset.card_eq_zero.mp (huniform S hS)]
    simpa [refinedBound] using Finset.card_le_card hsub
  | succ r ih =>
    have hdegree : ∀ x, (family.filter (fun S => x ∈ S)).card ≤ refinedBound p r := by
      intro x
      have hb := ih (residualLink family {x})
        (by simpa using (residualLink_uniform (core := {x}) huniform))
        (residualLink_sunflowerFree hfree)
      simpa [card_residualLink, upperStar] using hb
    have hb := card_le_refined_step family (r + 1) p (refinedBound p r)
      (by omega) (refinedBound_pos hp r) huniform hfree hdegree
    simpa [refinedBound] using hb

/-- Sharp upper bound for rank two and three petals. -/
theorem rank_two_three_petals_card_le_six {α : Type*} [DecidableEq α]
    (family : Finset (Finset α))
    (huniform : ∀ S ∈ family, S.card = 2)
    (hfree : IsSunflowerFree family 3) : family.card ≤ 6 := by
  have h := refined_sunflower_bound family 2 3 (by decide) huniform hfree
  norm_num [refinedBound] at h
  exact h


/-- Two disjoint triangles attain the rank-two, three-petal upper bound. -/
def twoTriangles : Finset (Finset (Fin 6)) :=
  {{0, 1}, {1, 2}, {0, 2}, {3, 4}, {4, 5}, {3, 5}}

theorem twoTriangles_card : twoTriangles.card = 6 := by decide

theorem twoTriangles_uniform : ∀ S ∈ twoTriangles, S.card = 2 := by decide

set_option maxRecDepth 4000 in
private theorem twoTriangles_no_sunflower_triple :
    ∀ S ∈ twoTriangles, ∀ T ∈ twoTriangles, ∀ U ∈ twoTriangles,
    S ≠ T → S ≠ U → T ≠ U →
      ¬ (S ∩ T = S ∩ U ∧ S ∩ T = T ∩ U) := by decide

theorem twoTriangles_sunflower_free : IsSunflowerFree twoTriangles 3 := by
  intro family hsub hsun
  obtain ⟨S, T, U, hST, hSU, hTU, hfamily⟩ :=
    Finset.card_eq_three.mp hsun.1
  have hS : S ∈ family := by simp [hfamily]
  have hT : T ∈ family := by simp [hfamily]
  have hU : U ∈ family := by simp [hfamily]
  obtain ⟨core, hcore⟩ := hsun.2
  apply twoTriangles_no_sunflower_triple S (hsub hS) T (hsub hT) U
    (hsub hU) hST hSU hTU
  exact ⟨(hcore S T hS hT hST).trans (hcore S U hS hU hSU).symm,
    (hcore S T hS hT hST).trans (hcore T U hT hU hTU).symm⟩

/-- This recurrence never exceeds the inherited factorial estimate. -/
theorem refinedBound_le_factorial (p r : ℕ) :
    refinedBound p r ≤ (p - 1) ^ r * r.factorial := by
  induction r with
  | zero => simp [refinedBound]
  | succ r ih =>
    calc
      _ ≤ (p - 1) * ((r + 1) * refinedBound p r) :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ ≤ (p - 1) * ((r + 1) * ((p - 1) ^ r * r.factorial)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ih)
      _ = _ := by rw [Nat.factorial_succ, pow_succ]; ring

/-- Exact-size obstructions must also exceed the refined recurrence. -/
theorem critical_refined_obstruction {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r q p : ℕ) (hp : 2 ≤ p)
    (huniform : ∀ S ∈ family, S.card = r)
    (hfree : IsSunflowerFree family p)
    (hcard : family.card = q ^ r + 1) : q ^ r < refinedBound p r := by
  have hb := refined_sunflower_bound family r p hp huniform hfree
  omega

/-- Concrete finite-rank exclusion, checked by the kernel. -/
theorem three_petals_base_four_low_ranks (r : ℕ) (hr : r ≤ 4) :
    refinedBound 3 r ≤ 4 ^ r := by
  interval_cases r <;> norm_num [refinedBound]

/-- Any exact-size base-four, three-petal obstruction starts after rank four. -/
theorem base_four_critical_rank_ge_five {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r : ℕ)
    (huniform : ∀ S ∈ family, S.card = r)
    (hfree : IsSunflowerFree family 3)
    (hcard : family.card = 4 ^ r + 1) : 5 ≤ r := by
  have hb := critical_refined_obstruction family r 4 3 (by decide) huniform hfree hcard
  by_contra hnot
  have hc := three_petals_base_four_low_ranks r (by omega)
  omega

/-- Singleton codegrees force a lower bound on support in the critical normal form. -/
theorem critical_support_card_gt {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r q : ℕ)
    (hr : 0 < r)
    (huniform : ∀ S ∈ family, S.card = r)
    (hcard : family.card = q ^ r + 1)
    (hdegree : ∀ x, (family.filter (fun S => x ∈ S)).card ≤ q ^ (r - 1)) :
    r * q < (support family).card := by
  classical
  have hcount : family.card * r =
      ∑ x ∈ support family, (family.filter (fun S => x ∈ S)).card := by
    rw [← incidence_sum_eq]
    calc
      _ = ∑ _S ∈ family, r := by simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [Finset.inter_eq_left.mpr (member_subset_support hS), huniform S hS]
  have hb : family.card * r ≤ (support family).card * q ^ (r - 1) := by
    rw [hcount]
    calc
      _ ≤ ∑ _x ∈ support family, q ^ (r - 1) :=
        Finset.sum_le_sum (fun x _ => hdegree x)
      _ = _ := by simp
  have hp : q ^ r = q * q ^ (r - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ r)]
  rw [hcard, hp] at hb
  by_contra hn
  have hle : (support family).card * q ^ (r - 1) ≤
      (r * q) * q ^ (r - 1) := Nat.mul_le_mul_right _ (Nat.le_of_not_gt hn)
  nlinarith

end Erdos20Incidence

