import SunflowerLean.Erdos20V11HighSupport
import SunflowerLean.Erdos20V10HighParity

namespace Erdos20V11HighEdgeCounts
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20V8Boundary Erdos20DegreeCongruences Erdos20V9HighGraph
open Erdos20V10HighTriangle Erdos20V8DesignCounts Erdos20V10HighParity

/-- A residual point of a high edge has five incidences with each endpoint
and exactly two incidences containing both endpoints. -/
theorem high_edge_residual_point_codegrees {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) (y : α) (hy : y ∈ highNeighbors F x)
    (u : α) (huU : u ∈ edgeSupport F x y) :
    (upperStar F {x,u}).card=5 ∧ (upperStar F {y,u}).card=5 ∧
      (upperStar F {x,y,u}).card=2 := by
  obtain ⟨hux,huy,R,hR,hxR,hyR,huR⟩ := (mem_edgeSupport_iff F x y u).mp huU
  obtain ⟨hyH,hyx,_⟩ := (mem_highNeighbors_iff F x y).mp hy
  have hpX := degree_twenty_pair_codegree_zero_or_five F hu hf x u hux.symm (Finset.mem_filter.mp hx).2
  have hpY := degree_twenty_pair_codegree_zero_or_five F hu hf y u huy.symm (Finset.mem_filter.mp hyH).2
  have hpXY := degree_twenty_triple_codegree_zero_or_two F hu hf x y u hyx.symm hux.symm huy.symm hx
  have hposX : 0 < (upperStar F {x,u}).card := Finset.card_pos.mpr ⟨R,mem_upperStar_iff.mpr
    ⟨hR,by simp [Finset.insert_subset_iff,hxR,huR]⟩⟩
  have hposY : 0 < (upperStar F {y,u}).card := Finset.card_pos.mpr ⟨R,mem_upperStar_iff.mpr
    ⟨hR,by simp [Finset.insert_subset_iff,hyR,huR]⟩⟩
  have hposXY : 0 < (upperStar F {x,y,u}).card := Finset.card_pos.mpr ⟨R,mem_upperStar_iff.mpr
    ⟨hR,by simp [Finset.insert_subset_iff,hxR,hyR,huR]⟩⟩
  omega

/-- Exactly eight members through a residual point contain at least one high
edge endpoint. This sharpens the elementary union bound ten. -/
theorem high_edge_residual_point_inside_card_eight {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) (y : α) (hy : y ∈ highNeighbors F x)
    (u : α) (huU : u ∈ edgeSupport F x y) :
    (F.filter (fun R => u ∈ R ∧ (x ∈ R ∨ y ∈ R))).card=8 := by
  classical
  obtain ⟨hX,hY,hXY⟩ := high_edge_residual_point_codegrees F hu hf x hx y hy u huU
  have hi : upperStar F {x,u} ∩ upperStar F {y,u} = upperStar F {x,y,u} := by
    ext R
    simp only [upperStar,Finset.mem_inter,Finset.mem_filter,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    tauto
  have he : F.filter (fun R => u ∈ R ∧ (x ∈ R ∨ y ∈ R)) =
      upperStar F {x,u} ∪ upperStar F {y,u} := by
    ext R
    simp only [upperStar,Finset.mem_union,Finset.mem_filter,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    tauto
  have hcard := Finset.card_union_add_card_inter (upperStar F {x,u}) (upperStar F {y,u})
  rw [hi,hX,hY,hXY] at hcard
  rw [he]
  omega

end Erdos20V11HighEdgeCounts
