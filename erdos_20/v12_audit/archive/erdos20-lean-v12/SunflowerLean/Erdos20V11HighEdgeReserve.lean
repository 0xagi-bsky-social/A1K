import SunflowerLean.Erdos20V11EdgePairs
import SunflowerLean.Erdos20V11CensusCapacity

namespace Erdos20V11HighEdgeReserve
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence Erdos20V8Boundary
open Erdos20V9HighGraph Erdos20V10HighTriangle Erdos20DesignNormalForm
open Erdos20V9HighCompatibility Erdos20V11EdgePairs

/-- Three distinct original members reserve capacity for each admissible
cycle pair: one contains both high endpoints and two contain one endpoint each. -/
theorem allowed_pair_three_reserved_members {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) (y : α) (hy : y ∈ highNeighbors F x)
    (A : Finset (Finset α)) (hAL : A ⊆ residualLink F {x})
    (heU : edgeSupport F x y = (support A).erase y)
    (e : Fin 6 ↪ α) (he : A = D.image (fun P => P.image e))
    (a b : Fin 6) (ha : e a=y) (C : Finset (Fin 6)) (hC : C ∈ allowedPairs a b) :
    3 ≤ (upperStar (F.filter (fun R => x ∈ R ∨ y ∈ R)) (C.image e)).card := by
  classical
  obtain ⟨hC2,haC,hbC,hcycle⟩ := (Finset.mem_filter.mp hC).2
  obtain ⟨P,hP,haP,hCP⟩ := allowedPairs_avoiding_block a b C hC
  have hPA : P.image e ∈ A := by rw [he]; exact Finset.mem_image.mpr ⟨P,hP,rfl⟩
  have hCA : (insert a C).image e ∈ A := by rw [he]; exact Finset.mem_image.mpr ⟨insert a C,hcycle,rfl⟩
  have hxP := point_not_mem_residue F x _ (hAL hPA)
  have hyP : y ∉ P.image e := by rw [← ha]; simpa using haP
  have hPU : P.image e ⊆ edgeSupport F x y := by
    rw [heU]
    intro u huP
    exact Finset.mem_erase.mpr ⟨fun heq => hyP (heq ▸ huP),member_subset_support hPA huP⟩
  have hPy := high_edge_single_residue_transfer F hu hf x hx y hy _ (hAL hPA) hPU
  let R0 := insert x ((insert a C).image e)
  let R1 := insert x (P.image e)
  let R2 := insert y (P.image e)
  have hR0 : R0 ∈ F := by simpa only [R0,Finset.singleton_union] using core_union_residual_mem_family (hAL hCA)
  have hR1 : R1 ∈ F := by simpa [R1] using core_union_residual_mem_family (hAL hPA)
  have hR2 : R2 ∈ F := by simpa [R2] using core_union_residual_mem_family hPy
  have hxy : x ≠ y := ((mem_highNeighbors_iff F x y).mp hy).2.1.symm
  have hx0 : x ∈ R0 := by simp [R0]
  have hy0 : y ∈ R0 := by simp [R0,← ha]
  have hx1 : x ∈ R1 := by simp [R1]
  have hy1 : y ∉ R1 := by simp [R1,hxy.symm,hyP]
  have hy2 : y ∈ R2 := by simp [R2]
  have hx2 : x ∉ R2 := by simp [R2,hxy,hxP]
  have h01 : R0 ≠ R1 := fun h => hy1 (h ▸ hy0)
  have h02 : R0 ≠ R2 := fun h => hx2 (h ▸ hx0)
  have h12 : R1 ≠ R2 := fun h => hx2 (h ▸ hx1)
  have hC0 : C.image e ⊆ R0 := by
    intro u huC
    exact Finset.mem_insert_of_mem (Finset.image_subset_image (Finset.subset_insert _ _) huC)
  have hC1 : C.image e ⊆ R1 := fun u huC => Finset.mem_insert_of_mem (Finset.image_subset_image hCP huC)
  have hC2' : C.image e ⊆ R2 := fun u huC => Finset.mem_insert_of_mem (Finset.image_subset_image hCP huC)
  have hsub : ({R0,R1,R2} : Finset (Finset α)) ⊆
      upperStar (F.filter (fun R => x ∈ R ∨ y ∈ R)) (C.image e) := by
    intro R hR
    simp only [Finset.mem_insert,Finset.mem_singleton] at hR
    rcases hR with rfl | rfl | rfl
    · exact mem_upperStar_iff.mpr ⟨Finset.mem_filter.mpr ⟨hR0,Or.inl hx0⟩,hC0⟩
    · exact mem_upperStar_iff.mpr ⟨Finset.mem_filter.mpr ⟨hR1,Or.inl hx1⟩,hC1⟩
    · exact mem_upperStar_iff.mpr ⟨Finset.mem_filter.mpr ⟨hR2,Or.inr hy2⟩,hC2'⟩
  have hcard : ({R0,R1,R2} : Finset (Finset α)).card=3 := by simp [h01,h02,h12]
  simpa [hcard] using Finset.card_le_card hsub

/-- An admissible pair has the inherited universal pair-star capacity six. -/
theorem allowed_pair_star_card_le_six {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (e : Fin 6 ↪ α) (a b : Fin 6) (C : Finset (Fin 6)) (hC : C ∈ allowedPairs a b) :
    (upperStar F (C.image e)).card ≤ 6 := by
  have hC2 : (C.image e).card=2 := by
    rw [Finset.card_image_of_injective _ e.injective]
    exact (Finset.mem_filter.mp hC).2.1
  obtain ⟨u,v,huv,he⟩ := Finset.card_eq_two.mp hC2
  rw [he]
  exact Erdos20V11Census.rank_four_pair_codegree_le_six F hu hf u v huv

end Erdos20V11HighEdgeReserve
