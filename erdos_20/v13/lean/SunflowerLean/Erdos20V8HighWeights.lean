import SunflowerLean.Erdos20V8DesignCounts
import SunflowerLean.Erdos20V8Boundary

/-! Reciprocal high-point incidence weights, derived from the complete extremal
triple classification and exact design block counts. -/
namespace Erdos20V8HighWeights
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20V8DesignCounts Erdos20V8Boundary Erdos20DegreeCongruences

/-- The weighted sum on a residual triple link. -/
def linkWeight {α : Type*} [DecidableEq α] (L : Finset (Finset α)) (H : Finset α) : ℕ :=
  ∑ P ∈ L, 6 / (1 + (P ∩ H).card)

/-- Exact evaluation of the three possible intersection classes. -/
theorem linkWeight_eq_block_counts
    {α : Type*} [DecidableEq α] (L : Finset (Finset α)) (H : Finset α)
    (hcap : ∀ P ∈ L, (P ∩ H).card ≤ 2) :
    linkWeight L H = 6 * blockCount L H 0 + 3 * blockCount L H 1 + 2 * blockCount L H 2 := by
  classical
  unfold linkWeight blockCount
  simp only [Finset.card_filter,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro P hP
  have hc := hcap P hP
  rcases (show (P ∩ H).card = 0 ∨ (P ∩ H).card = 1 ∨ (P ∩ H).card = 2 by omega) with h | h | h <;> simp [h]

/-- The four admissible weights of a twenty-triple link with at least four
supported distinguished points and at most two in each block. -/
theorem twenty_link_weight_four_values
    {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hu : ∀ P ∈ L, P.card = 3) (hf : IsSunflowerFree L 3) (hc : L.card = 20)
    (H : Finset α) (hhigh : 4 ≤ (H ∩ support L).card)
    (hcap : ∀ P ∈ L, (P ∩ H).card ≤ 2) :
    linkWeight L H = 72 ∨ linkWeight L H = 68 ∨ linkWeight L H = 61 ∨ linkWeight L H = 54 := by
  classical
  obtain ⟨A,hAL,hAc,hAi⟩ := Erdos20ExtremalTwenty.extremal_twenty_contains_intersecting_ten L hu hf hc
  let B := L \ A
  have hBL : B ⊆ L := Finset.sdiff_subset
  obtain ⟨hBc,hBi,hdis,_,_,_⟩ :=
    Erdos20DesignSeparation.extremal_twenty_complement_design L A hu hf hAL hAi hAc hc
  have heq : A ∪ B = L := Finset.union_sdiff_of_subset hAL
  have hdisAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro P hPA hPB
    exact (Finset.mem_sdiff.mp hPB).2 hPA
  have hsupport : support A ∪ support B = support L := by
    rw [← heq]
    ext z
    simp only [support,Finset.mem_union,Finset.mem_biUnion,Finset.mem_union]
    aesop
  have hsum : (H ∩ support A).card + (H ∩ support B).card = (H ∩ support L).card := by
    rw [← hsupport,Finset.inter_union_distrib_left,Finset.card_union_of_disjoint]
    exact hdis.mono Finset.inter_subset_right Finset.inter_subset_right
  have hAf : IsSunflowerFree A 3 := fun G hG hg => hf G (hG.trans hAL) hg
  have hBf : IsSunflowerFree B 3 := fun G hG hg => hf G (hG.trans hBL) hg
  have hcapA : ∀ P ∈ A, (P ∩ (H ∩ support A)).card ≤ 2 := by
    intro P hP
    exact (Finset.card_le_card (Finset.inter_subset_inter_left Finset.inter_subset_left)).trans (hcap P (hAL hP))
  have hcapB : ∀ P ∈ B, (P ∩ (H ∩ support B)).card ≤ 2 := by
    intro P hP
    exact (Finset.card_le_card (Finset.inter_subset_inter_left Finset.inter_subset_left)).trans (hcap P (hBL hP))
  have ha := ten_design_block_counts A (fun P hP => hu P (hAL hP)) hAf hAi hAc
    (H ∩ support A) Finset.inter_subset_right hcapA
  have hb := ten_design_block_counts B (fun P hP => hu P (hBL hP)) hBf hBi hBc
    (H ∩ support B) Finset.inter_subset_right hcapB
  simp only [blockCount_restrict_support] at ha hb
  have heval := linkWeight_eq_block_counts L H hcap
  have h0 := blockCount_union A B H 0 hdisAB
  have h1 := blockCount_union A B H 1 hdisAB
  have h2 := blockCount_union A B H 2 hdisAB
  rw [heq] at h0 h1 h2
  clear * - ha hb hsum hhigh heval h0 h1 h2
  rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;> omega

/-- Removing a distinguished point lowers the distinguished intersection size
by exactly one. -/
theorem residual_inter_card
    {α : Type*} [DecidableEq α] (S H : Finset α) (x : α)
    (hxS : x ∈ S) (hxH : x ∈ H) :
    (S ∩ H).card = 1 + ((S \ {x}) ∩ H).card := by
  have he : S ∩ H = insert x ((S \ {x}) ∩ H) := by
    ext y
    simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_sdiff,Finset.mem_singleton]
    constructor
    · intro h
      by_cases hy : y=x
      · exact Or.inl hy
      · exact Or.inr ⟨⟨h.1,hy⟩,h.2⟩
    · rintro (rfl | h)
      · exact ⟨hxS,hxH⟩
      · exact ⟨h.1.1,h.2⟩
  rw [he,Finset.card_insert_of_notMem (by simp)]
  omega

/-- The star weight transports exactly to the residual-link weight. -/
theorem pointWeight_eq_linkWeight
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (H : Finset α)
    (x : α) (hxH : x ∈ H) :
    pointWeight F H x = linkWeight (residualLink F {x}) H := by
  unfold pointWeight linkWeight residualLink
  rw [Finset.sum_image]
  · simp only [upperStar,Finset.singleton_subset_iff]
    apply Finset.sum_congr rfl
    intro S hS
    rw [residual_inter_card S H x (Finset.mem_filter.mp hS).2 hxH]
  · exact sdiff_injOn_upperStar F {x}

/-- Residual points remain in the original support. -/
theorem residual_support_subset
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (C : Finset α) :
    support (residualLink F C) ⊆ support F := by
  intro y hy
  obtain ⟨P,hP,hyP⟩ := Finset.mem_biUnion.mp hy
  obtain ⟨S,hS,_,hSP⟩ := mem_residualLink_iff.mp hP
  rw [← hSP] at hyP
  exact member_subset_support hS (Finset.mem_sdiff.mp hyP).1

/-- For an eighty-three-member family with only degrees nineteen and twenty,
every high point has one of the four rigorously derived reciprocal weights. -/
theorem high_point_weight_four_values
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3) (hc : F.card = 83)
    (hp : ∀ y ∈ support F, degree F y = 19 ∨ degree F y = 20)
    (hm : ∀ R ∈ F, (R ∩ highPoints F).card ≤ 3)
    (x : α) (hx : x ∈ highPoints F) :
    pointWeight F (highPoints F) x = 72 ∨
    pointWeight F (highPoints F) x = 68 ∨
    pointWeight F (highPoints F) x = 61 ∨
    pointWeight F (highPoints F) x = 54 := by
  classical
  let L := residualLink F {x}
  have hd : degree F x = 20 := (Finset.mem_filter.mp hx).2
  have huL : ∀ P ∈ L, P.card = 3 := by
    simpa using residualLink_uniform (core := ({x} : Finset α)) hu
  have hfL : IsSunflowerFree L 3 := residualLink_sunflowerFree hf
  have hcL : L.card = 20 := by
    simpa [L,card_residualLink,upperStar,degree] using hd
  have hsL : (support L).card = 12 :=
    (Erdos20ExtremalTwenty.extremal_twenty_regular_twelve L huL hfL hcL).1
  have hlow := (degree_classes_of_eighty_three F hu hc hp).2.2
  have hsub : support L \ highPoints F ⊆ (support F).filter (fun y => degree F y = 19) := by
    intro y hy
    obtain ⟨hyL,hyH⟩ := Finset.mem_sdiff.mp hy
    have hyF : y ∈ support F := residual_support_subset F {x} hyL
    apply Finset.mem_filter.mpr
    refine ⟨hyF,?_⟩
    rcases hp y hyF with hy19 | hy20
    · exact hy19
    · exact False.elim (hyH (Finset.mem_filter.mpr ⟨hyF,hy20⟩))
  have hdif : (support L \ highPoints F).card ≤ 8 := by
    simpa [hlow] using Finset.card_le_card hsub
  have hsum := Finset.card_sdiff_add_card_inter (support L) (highPoints F)
  have hhigh : 4 ≤ (highPoints F ∩ support L).card := by
    rw [Finset.inter_comm] at hsum
    omega
  have hcap : ∀ P ∈ L, (P ∩ highPoints F).card ≤ 2 := by
    intro P hP
    obtain ⟨S,hS,hxS,hSP⟩ := mem_residualLink_iff.mp hP
    have hcard := residual_inter_card S (highPoints F) x (Finset.singleton_subset_iff.mp hxS) hx
    have hbound := hm S hS
    rw [hSP] at hcard
    omega
  rw [pointWeight_eq_linkWeight F (highPoints F) x hx]
  exact twenty_link_weight_four_values L huL hfL hcL (highPoints F) hhigh hcap

end Erdos20V8HighWeights
