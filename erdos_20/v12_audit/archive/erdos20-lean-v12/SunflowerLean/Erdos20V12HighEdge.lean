import SunflowerLean.Erdos20V11EdgeThird
import SunflowerLean.Erdos20V11HighCommon

namespace Erdos20V12HighEdge
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence Erdos20RankThree
open Erdos20V8Boundary Erdos20DegreeCongruences Erdos20V9HighGraph
open Erdos20V10HighTriangle Erdos20V11HighSupport Erdos20V11EdgeThird
open Erdos20V9HighCompatibility Erdos20DesignSeparation Erdos20ExtremalTransversals

/-- A high edge is incompatible with every third high point, without any
bound on the ambient support. A three-point residue would otherwise be a
transversal of an actual twenty-triple link. -/
theorem high_edge_excludes_third_high {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) (y : α) (hy : y ∈ highNeighbors F x)
    (z : α) (hz : z ∈ highPoints F) (hxz : x ≠ z) (hyz : y ≠ z) : False := by
  classical
  have hyH := ((mem_highNeighbors_iff F x y).mp hy).1
  have hxy : x ≠ y := ((mem_highNeighbors_iff F x y).mp hy).2.1.symm
  have hxNy := high_neighbor_symm F x y hx hy
  obtain ⟨hzNx,hzNy⟩ := third_high_nonadjacent_to_edge F hu hf x hx y hy z hz hxz hyz
  have hxNz : x ∉ highNeighbors F z := fun hn => hzNx (high_neighbor_symm F z x hz hn)
  have hyNz : y ∉ highNeighbors F z := fun hn => hzNy (high_neighbor_symm F z y hz hn)
  have hzLx := nonneighbor_not_mem_link_support F x z hz hzNx
  have hxLz := nonneighbor_not_mem_link_support F z x hx hxNz
  have hyLz := nonneighbor_not_mem_link_support F z y hyH hyNz
  have hdZU := high_edge_third_high_support_disjoint F hu hf x hx y hy z hz hxz hyz
  have hdUH := high_edge_support_disjoint_high F hu hf x hx y hy
  obtain ⟨A,hAL,hyA,hAc,hAu,hAf,hAi,hiso⟩ := component_at_high_neighbor F hu hf x hx y hy
  have heA := edgeSupport_eq_component_erase F x y hxy A hAL hyA hAc hAu hAf hAi hiso
  let L := residualLink F {x}
  let B := L \ A
  have huL : ∀ P ∈ L, P.card=3 := by
    simpa using residualLink_uniform (core := ({x} : Finset α)) hu
  have hcL : L.card=20 := (high_link_twenty_and_support_twelve F hu hf x hx).1
  obtain ⟨hBc,hBi,hdAB,_⟩ := extremal_twenty_complement_design L A huL
    (residualLink_sunflowerFree hf) hAL hAi hAc hcL
  obtain ⟨Q,hQB⟩ := Finset.card_pos.mp (show 0<B.card by dsimp only [B]; omega)
  have hQL : Q ∈ residualLink F {x} := (Finset.mem_sdiff.mp hQB).1
  have hQ3 : Q.card=3 := huL Q hQL
  have hT : insert x Q ∈ F := by simpa using core_union_residual_mem_family hQL
  obtain ⟨S,hS,hyS,hsubS⟩ := high_edge_has_single_center_member F hu hf y hyH x hxNy
  have hsubS' : S ⊆ insert y (edgeSupport F x y) := by
    simpa only [edgeSupport_comm F y x] using hsubS
  have hSA : S ⊆ support A := by
    intro u huS
    rcases Finset.mem_insert.mp (hsubS' huS) with rfl | huU
    · exact hyA
    · rw [heA] at huU
      exact (Finset.mem_erase.mp huU).2
  have hxS : x ∉ S := by
    intro hxS
    obtain ⟨P,hP,hxP⟩ := Finset.mem_biUnion.mp (hSA hxS)
    exact point_not_mem_residue F x P (hAL hP) hxP
  have hzS : z ∉ S := by
    intro hzS
    rcases Finset.mem_insert.mp (hsubS' hzS) with he | hzU
    · exact hyz he.symm
    · exact Finset.disjoint_left.mp hdUH hzU hz
  have hdST : Disjoint S (insert x Q) := by
    apply Finset.disjoint_left.mpr
    intro u huS huT
    rcases Finset.mem_insert.mp huT with rfl | huQ
    · exact hxS huS
    · exact Finset.disjoint_left.mp hdAB (hSA huS) (member_subset_support hQB huQ)
  have huZ : ∀ P ∈ residualLink F {z}, P.card=3 := by
    simpa using residualLink_uniform (core := ({z} : Finset α)) hu
  have hhit : ∀ P ∈ residualLink F {z}, (P ∩ Q).Nonempty := by
    intro P hP
    have hR : insert z P ∈ F := by simpa using core_union_residual_mem_family hP
    have hdSR : Disjoint S (insert z P) := by
      apply Finset.disjoint_left.mpr
      intro u huS huR
      rcases Finset.mem_insert.mp huR with rfl | huP
      · exact hzS huS
      · rcases Finset.mem_insert.mp (hsubS' huS) with rfl | huU
        · exact hyLz (member_subset_support hP huP)
        · exact Finset.disjoint_left.mp hdZU (member_subset_support hP huP) huU
    have hm := disjoint_anchor_family_intersecting F S hS ⟨y,hyS⟩ hf
      (insert x Q) (Finset.mem_filter.mpr ⟨hT,Finset.disjoint_iff_inter_eq_empty.mp hdST.symm⟩)
      (insert z P) (Finset.mem_filter.mpr ⟨hR,Finset.disjoint_iff_inter_eq_empty.mp hdSR.symm⟩)
      (Finset.insert_nonempty x Q) (Finset.insert_nonempty z P)
    obtain ⟨u,hu⟩ := hm
    obtain ⟨huT,huR⟩ := Finset.mem_inter.mp hu
    rcases Finset.mem_insert.mp huT with rfl | huQ
    · rcases Finset.mem_insert.mp huR with he | hxP
      · exact False.elim (hxz he)
      · exact False.elim (hxLz (member_subset_support hP hxP))
    · rcases Finset.mem_insert.mp huR with rfl | huP
      · exact False.elim (hzLx (member_subset_support hQL huQ))
      · exact ⟨u,Finset.mem_inter.mpr ⟨huP,huQ⟩⟩
  have hmin := extremal_twenty_transversal_card_ge_six _ huZ (residualLink_sunflowerFree hf)
    (high_link_twenty_and_support_twelve F hu hf z hz).1 Q hhit
  omega

/-- If a high edge exists, its two endpoints exhaust the high class. -/
theorem high_edge_exhausts_high_class {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) (y : α) (hy : y ∈ highNeighbors F x) :
    highPoints F = {x,y} := by
  have hyH := ((mem_highNeighbors_iff F x y).mp hy).1
  ext z
  simp only [Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro hz
    by_cases hzx : z=x
    · exact Or.inl hzx
    by_cases hzy : z=y
    · exact Or.inr hzy
    exact False.elim (high_edge_excludes_third_high F hu hf x hx y hy z hz (Ne.symm hzx) (Ne.symm hzy))
  · rintro (rfl | rfl) <;> assumption

end Erdos20V12HighEdge
