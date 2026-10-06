import SunflowerLean.Erdos20V8Stability

/-! Exact block counts of the ten-triple design relative to an independent
supported subset. These are proved by incidence identities, not assumed tables. -/
namespace Erdos20V8DesignCounts
open Erdos20StrictCore Erdos20BCWConditional Erdos20Incidence Erdos20V5Frontier Erdos20ExtremalTransversals

/-- Blocks classified by the size of their intersection with a distinguished set. -/
def blockCount {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (C : Finset α) (k : ℕ) : ℕ :=
  (F.filter (fun S => (S ∩ C).card = k)).card

/-- A subset of the six-point design support containing no block has at most three points. -/
theorem independent_supported_subset_card_le_three
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 10)
    (C : Finset α) (hCS : C ⊆ support F) (hind : ∀ S ∈ F, ¬ S ⊆ C) : C.card ≤ 3 := by
  have hhit : ∀ S ∈ F, (S ∩ (support F \ C)).Nonempty := by
    intro S hS
    obtain ⟨x,hxS,hxC⟩ := Finset.not_subset.mp (hind S hS)
    exact ⟨x,Finset.mem_inter.mpr ⟨hxS,Finset.mem_sdiff.mpr ⟨member_subset_support hS hxS,hxC⟩⟩⟩
  have hlow := intersecting_ten_transversal_card_ge_three F hu hf hi hc (support F \ C) hhit
  have hs := (intersecting_ten_design F hu hf hi hc).1
  have hle := Finset.card_le_card hCS
  rw [Finset.card_sdiff_of_subset hCS,hs] at hlow
  rw [hs] at hle
  omega

/-- Class counts add to the family size when every intersection has size at most two. -/
theorem block_counts_total
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (C : Finset α)
    (hcap : ∀ S ∈ F, (S ∩ C).card ≤ 2) :
    blockCount F C 0 + blockCount F C 1 + blockCount F C 2 = F.card := by
  classical
  calc
    _ = ∑ S ∈ F, ((if (S ∩ C).card = 0 then 1 else 0) +
        (if (S ∩ C).card = 1 then 1 else 0) + (if (S ∩ C).card = 2 then 1 else 0)) := by
      simp only [blockCount,Finset.card_filter,Finset.sum_add_distrib]
    _ = ∑ _S ∈ F, 1 := by
      apply Finset.sum_congr rfl
      intro S hS
      rcases (show (S ∩ C).card = 0 ∨ (S ∩ C).card = 1 ∨ (S ∩ C).card = 2 by have := hcap S hS; omega) with h | h | h <;> simp [h]
    _ = _ := by simp

/-- The first intersection moment is the number of one-point blocks plus
 twice the number of two-point blocks. -/
theorem block_counts_first_moment
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (C : Finset α)
    (hcap : ∀ S ∈ F, (S ∩ C).card ≤ 2) :
    (∑ S ∈ F, (S ∩ C).card) = blockCount F C 1 + 2 * blockCount F C 2 := by
  classical
  calc
    _ = ∑ S ∈ F, ((if (S ∩ C).card = 1 then 1 else 0) +
        2 * (if (S ∩ C).card = 2 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro S hS
      rcases (show (S ∩ C).card = 0 ∨ (S ∩ C).card = 1 ∨ (S ∩ C).card = 2 by have := hcap S hS; omega) with h | h | h <;> simp [h]
    _ = _ := by simp only [blockCount,Finset.card_filter,Finset.sum_add_distrib,Finset.mul_sum]

/-- Every two-point block contributes exactly one pair to the second moment. -/
theorem block_counts_second_moment
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (C : Finset α)
    (hcap : ∀ S ∈ F, (S ∩ C).card ≤ 2) :
    (∑ S ∈ F, ((S ∩ C).powersetCard 2).card) = blockCount F C 2 := by
  classical
  rw [blockCount,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.card_powersetCard]
  rcases (show (S ∩ C).card = 0 ∨ (S ∩ C).card = 1 ∨ (S ∩ C).card = 2 by have := hcap S hS; omega) with h | h | h <;> simp [h]

/-- Counting incidences between members and distinguished pairs in either order. -/
theorem pair_incidence_sum_eq
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (C : Finset α) :
    (∑ S ∈ F, ((S ∩ C).powersetCard 2).card) =
      ∑ P ∈ C.powersetCard 2, (F.filter (fun S => P ⊆ S)).card := by
  classical
  have hshape (S : Finset α) :
      (S ∩ C).powersetCard 2 = (C.powersetCard 2).filter (fun P => P ⊆ S) := by
    ext P
    simp only [Finset.mem_powersetCard,Finset.mem_filter,Finset.subset_inter_iff]
    tauto
  simp_rw [hshape,Finset.card_filter]
  exact Finset.sum_comm

/-- The exact class-count equations for an independent supported subset of the design. -/
theorem ten_design_block_count_equations
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 10)
    (C : Finset α) (hCS : C ⊆ support F)
    (hcap : ∀ S ∈ F, (S ∩ C).card ≤ 2) :
    C.card ≤ 3 ∧
      blockCount F C 0 + blockCount F C 1 + blockCount F C 2 = 10 ∧
      blockCount F C 1 + 2 * blockCount F C 2 = 5 * C.card ∧
      blockCount F C 2 = 2 * C.card.choose 2 := by
  obtain ⟨hs,hd,hp⟩ := intersecting_ten_design F hu hf hi hc
  have hcard : C.card ≤ 3 := independent_supported_subset_card_le_three F hu hf hi hc C hCS (by
    intro S hS hSC
    have hh := hcap S hS
    rw [Finset.inter_eq_left.mpr hSC,hu S hS] at hh
    omega)
  refine ⟨hcard,?_,?_,?_⟩
  · simpa [hc] using block_counts_total F C hcap
  · rw [← block_counts_first_moment F C hcap,incidence_sum_eq]
    calc
      _ = ∑ _x ∈ C, 5 := Finset.sum_congr rfl (fun x hx => hd x (hCS hx))
      _ = _ := by simp [Nat.mul_comm]
  · rw [← block_counts_second_moment F C hcap,pair_incidence_sum_eq]
    have hpair (P : Finset α) (hP : P ∈ C.powersetCard 2) :
        (F.filter (fun S => P ⊆ S)).card = 2 := by
      obtain ⟨hPC,hP2⟩ := Finset.mem_powersetCard.mp hP
      obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp hP2
      exact hp x (hCS (hPC (by simp))) y (hCS (hPC (by simp))) hxy
    calc
      _ = ∑ _P ∈ C.powersetCard 2, 2 := Finset.sum_congr rfl hpair
      _ = _ := by simp [Finset.card_powersetCard,Nat.mul_comm]

/-- Complete numerical profiles for the number of zero-, one- and two-point blocks. -/
theorem ten_design_block_counts
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 10)
    (C : Finset α) (hCS : C ⊆ support F)
    (hcap : ∀ S ∈ F, (S ∩ C).card ≤ 2) :
    (C.card = 0 ∧ blockCount F C 0 = 10 ∧ blockCount F C 1 = 0 ∧ blockCount F C 2 = 0) ∨
    (C.card = 1 ∧ blockCount F C 0 = 5 ∧ blockCount F C 1 = 5 ∧ blockCount F C 2 = 0) ∨
    (C.card = 2 ∧ blockCount F C 0 = 2 ∧ blockCount F C 1 = 6 ∧ blockCount F C 2 = 2) ∨
    (C.card = 3 ∧ blockCount F C 0 = 1 ∧ blockCount F C 1 = 3 ∧ blockCount F C 2 = 6) := by
  obtain ⟨hk,htotal,hfirst,hsecond⟩ := ten_design_block_count_equations F hu hf hi hc C hCS hcap
  rcases (show C.card=0 ∨ C.card=1 ∨ C.card=2 ∨ C.card=3 by omega) with h | h | h | h
  · simp only [h] at hsecond
    norm_num at hsecond
    exact Or.inl ⟨h,by omega,by omega,hsecond⟩
  · simp only [h] at hsecond
    norm_num at hsecond
    exact Or.inr (Or.inl ⟨h,by omega,by omega,hsecond⟩)
  · simp only [h] at hsecond
    norm_num at hsecond
    exact Or.inr (Or.inr (Or.inl ⟨h,by omega,by omega,hsecond⟩))
  · simp only [h] at hsecond
    norm_num at hsecond
    exact Or.inr (Or.inr (Or.inr ⟨h,by omega,by omega,hsecond⟩))

/-- Intersections only depend on the distinguished points inside the support. -/
theorem blockCount_restrict_support
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (C : Finset α) (k : ℕ) :
    blockCount F (C ∩ support F) k = blockCount F C k := by
  unfold blockCount
  congr 1
  apply Finset.filter_congr
  intro S hS
  have hEq : S ∩ (C ∩ support F) = S ∩ C := by
    ext x
    simp only [Finset.mem_inter]
    constructor
    · tauto
    · intro h
      exact ⟨h.1,h.2,member_subset_support hS h.1⟩
  rw [hEq]

/-- Block counts add across disjoint families. -/
theorem blockCount_union
    {α : Type*} [DecidableEq α] (F G : Finset (Finset α))
    (C : Finset α) (k : ℕ) (hd : Disjoint F G) :
    blockCount (F ∪ G) C k = blockCount F C k + blockCount G C k := by
  unfold blockCount
  rw [Finset.filter_union,Finset.card_union_of_disjoint]
  exact hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- Every pair containing a degree-twenty point has codegree zero or five. -/
theorem degree_twenty_pair_codegree_zero_or_five
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (x y : α) (hxy : x ≠ y) (hd : (F.filter (fun S => x ∈ S)).card = 20) :
    (upperStar F {x,y}).card = 0 ∨ (upperStar F {x,y}).card = 5 := by
  let L := residualLink F {x}
  have huL : ∀ S ∈ L, S.card = 3 := by
    simpa using residualLink_uniform (core := ({x} : Finset α)) hu
  have hfL : IsSunflowerFree L 3 := residualLink_sunflowerFree hf
  have hcL : L.card = 20 := by
    simpa [L,card_residualLink,upperStar] using hd
  have hdL := (Erdos20ExtremalTwenty.extremal_twenty_regular_twelve L huL hfL hcL).2
  have heq : (L.filter (fun P => y ∈ P)).card = (upperStar F {x,y}).card := by
    simpa [L,Finset.pair_comm] using card_filter_residualLink F ({x} : Finset α) {y} (by simpa using hxy.symm)
  by_cases hy : y ∈ support L
  · exact Or.inr (heq.symm.trans (hdL y hy))
  · left
    rw [← heq]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro P hP
    exact hy (member_subset_support (Finset.mem_filter.mp hP).1 (Finset.mem_filter.mp hP).2)

end Erdos20V8DesignCounts
