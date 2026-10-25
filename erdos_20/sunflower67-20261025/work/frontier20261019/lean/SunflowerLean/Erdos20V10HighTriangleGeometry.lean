import SunflowerLean.Erdos20V10HighTriangle

namespace Erdos20V10HighTriangle
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20V8Boundary Erdos20DegreeCongruences Erdos20V9HighGraph
open Erdos20V9HighCompatibility Erdos20V9HighIncidence Erdos20V5Frontier

/-- Every residual point of an edge between high points is low. -/
theorem high_edge_support_disjoint_high {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) (y : α) (hy : y ∈ highNeighbors F x) :
    Disjoint (edgeSupport F x y) (highPoints F) := by
  obtain ⟨hyH,hyx,_⟩ := (mem_highNeighbors_iff F x y).mp hy
  obtain ⟨A,hAL,hyA,hAc,hAu,hAf,hAi,hiso⟩ := component_at_high_neighbor F hu hf x hx y hy
  have he := edgeSupport_eq_component_erase F x y hyx.symm A hAL hyA hAc hAu hAf hAi hiso
  have hsmall := ten_design_distinguished_support_card_le_one A hAu hAf hAi hAc
    (highPoints F) (fun P hP => high_link_cap_one F (member_high_points_card_le_two F hu hf) x hx P (hAL hP))
  apply Finset.disjoint_left.mpr
  intro u huU huH
  rw [he] at huU
  obtain ⟨huy,huA⟩ := Finset.mem_erase.mp huU
  exact huy (Finset.card_le_one.mp hsmall u (Finset.mem_inter.mpr ⟨huA,huH⟩)
    y (Finset.mem_inter.mpr ⟨hyA,hyH⟩))

/-- Distinct high edges incident to the same high point have disjoint residual supports. -/
theorem incident_high_edge_supports_disjoint {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) (y z : α)
    (hy : y ∈ highNeighbors F x) (hz : z ∈ highNeighbors F x) (hyz : y ≠ z) :
    Disjoint (edgeSupport F x y) (edgeSupport F x z) := by
  obtain ⟨hyH,hyx,_⟩ := (mem_highNeighbors_iff F x y).mp hy
  obtain ⟨hzH,hzx,_⟩ := (mem_highNeighbors_iff F x z).mp hz
  obtain ⟨A,hAL,hyA,hAc,hAu,hAf,hAi,hiso⟩ := component_at_high_neighbor F hu hf x hx y hy
  have he := edgeSupport_eq_component_erase F x y hyx.symm A hAL hyA hAc hAu hAf hAi hiso
  have hsmall := ten_design_distinguished_support_card_le_one A hAu hAf hAi hAc
    (highPoints F) (fun P hP => high_link_cap_one F (member_high_points_card_le_two F hu hf) x hx P (hAL hP))
  apply Finset.disjoint_left.mpr
  intro u huY huZ
  rw [he] at huY
  have huA := (Finset.mem_erase.mp huY).2
  obtain ⟨hux,_,R,hR,hxR,hzR,huR⟩ := (mem_edgeSupport_iff F x z u).mp huZ
  have hP : R \ {x} ∈ residualLink F {x} :=
    mem_residualLink_iff.mpr ⟨R,hR,by simpa using hxR,rfl⟩
  have hPA := hiso _ hP ⟨u,Finset.mem_inter.mpr ⟨by simp [huR,hux],huA⟩⟩
  have hzA := member_subset_support hPA (show z ∈ R \ {x} by simp [hzR,hzx])
  exact hyz (Finset.card_le_one.mp hsmall y (Finset.mem_inter.mpr ⟨hyA,hyH⟩)
    z (Finset.mem_inter.mpr ⟨hzA,hzH⟩))

/-- A high edge supplies an actual member containing its first endpoint and
otherwise only points of the edge's residual support. -/
theorem high_edge_has_single_center_member {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) (y : α) (hy : y ∈ highNeighbors F x) :
    ∃ R ∈ F, x ∈ R ∧ R ⊆ insert x (edgeSupport F x y) := by
  classical
  obtain ⟨_,hyx,_⟩ := (mem_highNeighbors_iff F x y).mp hy
  obtain ⟨A,hAL,hyA,hAc,hAu,hAf,hAi,hiso⟩ := component_at_high_neighbor F hu hf x hx y hy
  have he := edgeSupport_eq_component_erase F x y hyx.symm A hAL hyA hAc hAu hAf hAi hiso
  have hd := (intersecting_ten_design A hAu hAf hAi hAc).2.1 y hyA
  have hex : ∃ P ∈ A, y ∉ P := by
    by_contra hn
    push_neg at hn
    have hfilter : A.filter (fun P => y ∈ P)=A := Finset.filter_eq_self.mpr hn
    rw [hfilter,hAc] at hd
    omega
  obtain ⟨P,hPA,hyP⟩ := hex
  obtain ⟨R,hR,hxR,hRP⟩ := mem_residualLink_iff.mp (hAL hPA)
  refine ⟨R,hR,Finset.singleton_subset_iff.mp hxR,?_⟩
  intro u huR
  by_cases hux : u=x
  · simp [hux]
  · apply Finset.mem_insert_of_mem
    rw [he]
    have huP : u ∈ P := by rw [← hRP]; simp [huR,hux]
    exact Finset.mem_erase.mpr ⟨fun huy => hyP (huy ▸ huP),member_subset_support hPA huP⟩

/-- High adjacency is symmetric when both endpoints are high. -/
theorem high_neighbor_symm {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (x y : α) (hx : x ∈ highPoints F)
    (hy : y ∈ highNeighbors F x) : x ∈ highNeighbors F y := by
  obtain ⟨_,hyx,R,hR,hxR,hyR⟩ := (mem_highNeighbors_iff F x y).mp hy
  exact (mem_highNeighbors_iff F y x).mpr ⟨hx,hyx.symm,R,hR,hyR,hxR⟩

end Erdos20V10HighTriangle
