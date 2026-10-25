import SunflowerLean.Erdos20V10HighTriangleGeometry

namespace Erdos20V10HighTriangle
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence Erdos20RankThree
open Erdos20V8Boundary Erdos20DegreeCongruences Erdos20V9HighGraph

/-- Distinct distinguished centers appended to disjoint low supports stay disjoint. -/
theorem insert_centers_disjoint {α : Type*} [DecidableEq α]
    (H U V : Finset α) (x y : α) (hx : x ∈ H) (hy : y ∈ H) (hxy : x ≠ y)
    (hUH : Disjoint U H) (hVH : Disjoint V H) (hUV : Disjoint U V) :
    Disjoint (insert x U) (insert y V) := by
  apply Finset.disjoint_left.mpr
  intro u hu hv
  rcases Finset.mem_insert.mp hu with rfl | hu
  · rcases Finset.mem_insert.mp hv with he | hv
    · exact hxy he
    · exact Finset.disjoint_left.mp hVH hv hx
  · rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Finset.disjoint_left.mp hUH hu hy
    · exact Finset.disjoint_left.mp hUV hu hv

/-- Three degree-twenty points cannot be mutually adjacent in the actual co-membership graph. -/
theorem no_high_triangle {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x y z : α) (hx : x ∈ highPoints F)
    (hyx : y ∈ highNeighbors F x) (hzy : z ∈ highNeighbors F y)
    (hxz : x ∈ highNeighbors F z) : False := by
  have hy := ((mem_highNeighbors_iff F x y).mp hyx).1
  have hz := ((mem_highNeighbors_iff F y z).mp hzy).1
  have hxy : x ≠ y := ((mem_highNeighbors_iff F x y).mp hyx).2.1.symm
  have hyz : y ≠ z := ((mem_highNeighbors_iff F y z).mp hzy).2.1.symm
  have hzx : z ≠ x := ((mem_highNeighbors_iff F z x).mp hxz).2.1.symm
  have hxy' := high_neighbor_symm F x y hx hyx
  have hyz' := high_neighbor_symm F y z hy hzy
  have hzx' := high_neighbor_symm F z x hz hxz
  obtain ⟨R,hR,hxR,hsubR⟩ := high_edge_has_single_center_member F hu hf x hx y hyx
  obtain ⟨S,hS,hyS,hsubS⟩ := high_edge_has_single_center_member F hu hf y hy z hzy
  obtain ⟨T,hT,hzT,hsubT⟩ := high_edge_has_single_center_member F hu hf z hz x hxz
  have hUH := high_edge_support_disjoint_high F hu hf x hx y hyx
  have hVH := high_edge_support_disjoint_high F hu hf y hy z hzy
  have hWH := high_edge_support_disjoint_high F hu hf z hz x hxz
  have hUV : Disjoint (edgeSupport F x y) (edgeSupport F y z) := by
    have h := incident_high_edge_supports_disjoint F hu hf y hy x z hxy' hzy hzx.symm
    rw [edgeSupport_comm F y x] at h
    exact h
  have hUW : Disjoint (edgeSupport F x y) (edgeSupport F z x) := by
    have h := incident_high_edge_supports_disjoint F hu hf x hx y z hyx hzx' hyz
    rw [edgeSupport_comm F x z] at h
    exact h
  have hVW : Disjoint (edgeSupport F y z) (edgeSupport F z x) := by
    have h := incident_high_edge_supports_disjoint F hu hf z hz y x hyz' hxz hxy.symm
    rw [edgeSupport_comm F z y] at h
    exact h
  have hRS : Disjoint R S := (insert_centers_disjoint (highPoints F) _ _ x y hx hy hxy hUH hVH hUV).mono hsubR hsubS
  have hRT : Disjoint R T := (insert_centers_disjoint (highPoints F) _ _ x z hx hz hzx.symm hUH hWH hUW).mono hsubR hsubT
  have hST : Disjoint S T := (insert_centers_disjoint (highPoints F) _ _ y z hy hz hyz hVH hWH hVW).mono hsubS hsubT
  have hmeet := disjoint_anchor_family_intersecting F R hR ⟨x,hxR⟩ hf S
    (Finset.mem_filter.mpr ⟨hS,Finset.disjoint_iff_inter_eq_empty.mp hRS.symm⟩) T
    (Finset.mem_filter.mpr ⟨hT,Finset.disjoint_iff_inter_eq_empty.mp hRT.symm⟩) ⟨y,hyS⟩ ⟨z,hzT⟩
  rw [Finset.disjoint_iff_inter_eq_empty.mp hST] at hmeet
  exact Finset.not_nonempty_empty hmeet

/-- The neighbors of a high point contain no adjacent pair. -/
theorem high_neighbors_pairwise_nonadjacent {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) (y z : α)
    (hy : y ∈ highNeighbors F x) (hz : z ∈ highNeighbors F x) :
    z ∉ highNeighbors F y := by
  intro hzy
  exact no_high_triangle F hu hf x y z hx hy hzy (high_neighbor_symm F x z hx hz)

end Erdos20V10HighTriangle
