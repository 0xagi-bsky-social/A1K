import SunflowerLean.Erdos20SharpTwenty

/-! Weighted cross-intersection bounds between triples and graph edges. -/
namespace Erdos20MixedCross
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20CrossBounds Erdos20RankThree Erdos20RankThreeEven
open Erdos20GraphEquality Erdos20SharpTriples Erdos20Tetrahedron

theorem triple_pair_degree_le_two {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S ∈ F, S.card = 3)
    (hf : IsSunflowerFree F 3) (C : Finset α) (hC : C.card = 2) :
    (F.filter (fun S => C ⊆ S)).card ≤ 2 := by
  have h := refined_sunflower_bound (residualLink F C) 1 3 (by decide)
    (by simpa [hC] using residualLink_uniform (core := C) hu)
    (residualLink_sunflowerFree hf)
  simpa [refinedBound, card_residualLink, upperStar] using h

/-- Two distinct intersecting edges cover a triple by their center or opposite pair. -/
theorem triples_cross_two_edges_card_le_eight {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (B C : Finset α)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hB : B.card = 2) (hC : C.card = 2) (hne : B ≠ C)
    (hBC : (B ∩ C).Nonempty)
    (hcrossB : ∀ S ∈ F, (S ∩ B).Nonempty)
    (hcrossC : ∀ S ∈ F, (S ∩ C).Nonempty) : F.card ≤ 8 := by
  classical
  obtain ⟨x,hx⟩ := hBC
  obtain ⟨hxB,hxC⟩ := Finset.mem_inter.mp hx
  obtain ⟨y,hy⟩ := Finset.card_eq_one.mp (show (B.erase x).card = 1 by
    rw [Finset.card_erase_of_mem hxB,hB])
  obtain ⟨z,hz⟩ := Finset.card_eq_one.mp (show (C.erase x).card = 1 by
    rw [Finset.card_erase_of_mem hxC,hC])
  have hBs : B = {x,y} := by rw [← Finset.insert_erase hxB,hy]
  have hCs : C = {x,z} := by rw [← Finset.insert_erase hxC,hz]
  have hyz : y ≠ z := by intro he; apply hne; rw [hBs,hCs,he]
  have hcover : F ⊆ (F.filter (fun S => x ∈ S)) ∪
      (F.filter (fun S => ({y,z} : Finset α) ⊆ S)) := by
    intro S hS
    by_cases hxS : x ∈ S
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hS,hxS⟩)
    · have hyS : y ∈ S := by
        obtain ⟨a,ha⟩ := hcrossB S hS
        obtain ⟨haS,haB⟩ := Finset.mem_inter.mp ha
        simp only [hBs,Finset.mem_insert,Finset.mem_singleton] at haB
        rcases haB with rfl | rfl
        · exact False.elim (hxS haS)
        · exact haS
      have hzS : z ∈ S := by
        obtain ⟨a,ha⟩ := hcrossC S hS
        obtain ⟨haS,haC⟩ := Finset.mem_inter.mp ha
        simp only [hCs,Finset.mem_insert,Finset.mem_singleton] at haC
        rcases haC with rfl | rfl
        · exact False.elim (hxS haS)
        · exact haS
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨hS,by simp [Finset.insert_subset_iff,hyS,hzS]⟩)
  have ha := Finset.card_le_card hcover
  have hb := Finset.card_union_le (F.filter (fun S => x ∈ S))
    (F.filter (fun S => ({y,z} : Finset α) ⊆ S))
  have hd := rank_three_degree_le_six F hu hf x
  have hp := triple_pair_degree_le_two F hu hf {y,z} (by simp [hyz])
  omega

/-- A triple meeting every edge of a triangle contains one of its pairs. -/
theorem triples_cross_triangle_card_le_six {α : Type*} [DecidableEq α]
    (F G : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (huG : ∀ S ∈ G, S.card = 2) (hfG : IsSunflowerFree G 3)
    (hiG : ∀ S ∈ G, ∀ T ∈ G, (S ∩ T).Nonempty) (hcG : G.card = 3)
    (hcross : ∀ S ∈ F, ∀ T ∈ G, (S ∩ T).Nonempty) : F.card ≤ 6 := by
  classical
  obtain ⟨x,y,z,hxy,hxz,hyz,hshape⟩ := intersecting_three_edges_triangle G huG
    (rank_two_three_petals_degree_le_two G huG hfG) hiG hcG
  let A : Finset α := {x,y,z}
  have hA : A.card = 3 := by simp [A,hxy,hxz,hyz]
  have hcover : F ⊆ (A.powersetCard 2).biUnion
      (fun C => F.filter (fun S => C ⊆ S)) := by
    intro S hS
    have hh : ∀ C ∈ A.powersetCard 2, (S ∩ C).Nonempty := by
      intro C hC
      apply hcross S hS
      rw [hshape]
      exact pair_subset_triangle_mem x y z C hC
    obtain ⟨C,hC,hCS⟩ := contains_pair_of_meets_every_pair_of_triple A S hA hh
    exact Finset.mem_biUnion.mpr ⟨C,hC,Finset.mem_filter.mpr ⟨hS,hCS⟩⟩
  calc
    F.card ≤ ((A.powersetCard 2).biUnion
      (fun C => F.filter (fun S => C ⊆ S))).card := Finset.card_le_card hcover
    _ ≤ ∑ C ∈ A.powersetCard 2, (F.filter (fun S => C ⊆ S)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _C ∈ A.powersetCard 2, 2 := Finset.sum_le_sum (fun C hC =>
      triple_pair_degree_le_two F hu hf C (Finset.mem_powersetCard.mp hC).2)
    _ = 6 := by simp [Finset.card_powersetCard,hA]

/-- The rank-three/rank-two weighted bound used by complementary rank-four traces. -/
theorem intersecting_triples_cross_edges_weighted {α : Type*} [DecidableEq α]
    (F G : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (huG : ∀ S ∈ G, S.card = 2) (hfG : IsSunflowerFree G 3)
    (hiG : ∀ S ∈ G, ∀ T ∈ G, (S ∩ T).Nonempty)
    (hcross : ∀ S ∈ F, ∀ T ∈ G, (S ∩ T).Nonempty) :
    F.card + 2 * G.card ≤ 12 := by
  have hF := intersecting_rank_three_card_le_ten F hu hf hi
  have hG := intersecting_rank_two_three_petals_card_le_three G huG hfG hiG
  by_cases hG1 : G.card ≤ 1
  · omega
  · by_cases hG2 : G.card = 2
    · obtain ⟨B,C,hBC,hshape⟩ := Finset.card_eq_two.mp hG2
      have hBG : B ∈ G := by simp [hshape]
      have hCG : C ∈ G := by simp [hshape]
      have hh := triples_cross_two_edges_card_le_eight F B C hu hf
        (huG B hBG) (huG C hCG) hBC (hiG B hBG C hCG)
        (fun S hS => hcross S hS B hBG) (fun S hS => hcross S hS C hCG)
      omega
    · have hh := triples_cross_triangle_card_le_six F G hu hf huG hfG hiG
        (by omega) hcross
      omega

end Erdos20MixedCross
