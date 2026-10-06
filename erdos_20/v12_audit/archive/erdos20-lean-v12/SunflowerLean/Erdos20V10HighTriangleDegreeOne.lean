import SunflowerLean.Erdos20V10HighTriangleTransfer

namespace Erdos20V10HighTriangle
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence Erdos20RankThree
open Erdos20V8Boundary Erdos20DegreeCongruences Erdos20V9HighGraph
open Erdos20V9HighCompatibility Erdos20V8Stability Erdos20DesignSeparation

/-- Three distinct centers cannot share an actual point-link residue. -/
theorem no_three_common_point_residue {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hf : IsSunflowerFree F 3) (x y z : α)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (P : Finset α)
    (hxP : P ∈ residualLink F {x}) (hyP : P ∈ residualLink F {y})
    (hzP : P ∈ residualLink F {z}) : False := by
  have hxnot := point_not_mem_residue F x P hxP
  have hynot := point_not_mem_residue F y P hyP
  have hznot := point_not_mem_residue F z P hzP
  have hRx : insert x P ∈ F := by simpa using core_union_residual_mem_family hxP
  have hRy : insert y P ∈ F := by simpa using core_union_residual_mem_family hyP
  have hRz : insert z P ∈ F := by simpa using core_union_residual_mem_family hzP
  have hxyR : insert x P ≠ insert y P := by
    intro he
    have hm : x ∈ insert y P := he ▸ Finset.mem_insert_self x P
    simp [hxy,hxnot] at hm
  have hxzR : insert x P ≠ insert z P := by
    intro he
    have hm : x ∈ insert z P := he ▸ Finset.mem_insert_self x P
    simp [hxz,hxnot] at hm
  have hyzR : insert y P ≠ insert z P := by
    intro he
    have hm : y ∈ insert z P := he ▸ Finset.mem_insert_self y P
    simp [hyz,hynot] at hm
  apply hf {insert x P,insert y P,insert z P}
  · intro R hR
    simp only [Finset.mem_insert,Finset.mem_singleton] at hR
    rcases hR with rfl | rfl | rfl <;> assumption
  · apply sunflower_three_of_intersections _ _ _ P hxyR hxzR hyzR
    all_goals ext u; simp only [Finset.mem_inter,Finset.mem_insert]; aesop

/-- Even a two-edge path of high points is impossible. -/
theorem no_two_high_neighbors {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (y : α) (hy : y ∈ highPoints F) (x z : α)
    (hxN : x ∈ highNeighbors F y) (hzN : z ∈ highNeighbors F y) (hxz : x ≠ z) : False := by
  classical
  have hx := ((mem_highNeighbors_iff F y x).mp hxN).1
  have hz := ((mem_highNeighbors_iff F y z).mp hzN).1
  have hxy : x ≠ y := ((mem_highNeighbors_iff F y x).mp hxN).2.1
  have hzy : z ≠ y := ((mem_highNeighbors_iff F y z).mp hzN).2.1
  have hyNx := high_neighbor_symm F y x hy hxN
  have hyNz := high_neighbor_symm F y z hy hzN
  have hzxNon : z ∉ highNeighbors F x := high_neighbors_pairwise_nonadjacent F hu hf y hy x z hxN hzN
  let L := residualLink F {x}
  have hLu : ∀ Q ∈ L, Q.card=3 := by simpa using residualLink_uniform (core := ({x} : Finset α)) hu
  have hLf : IsSunflowerFree L 3 := residualLink_sunflowerFree hf
  have hLc : L.card=20 := by simpa [L,card_residualLink,upperStar,degree] using (Finset.mem_filter.mp hx).2
  have hzL : z ∉ support L := fun hzL => hzxNon (Finset.mem_inter.mpr ⟨hzL,hz⟩)
  obtain ⟨A,hAL,hyA,hAc,hAu,hAf,hAi,hisoA⟩ := component_at_high_neighbor F hu hf x hx y hyNx
  let D := L \ A
  have hDsub : D ⊆ L := Finset.sdiff_subset
  have hDu : ∀ Q ∈ D, Q.card=3 := fun Q hQ => hLu Q (hDsub hQ)
  have hDf : IsSunflowerFree D 3 := fun J hJ hs => hLf J (hJ.trans hDsub) hs
  obtain ⟨hDc,hDi,hAD,_⟩ := extremal_twenty_complement_design L A hLu hLf hAL hAi hAc hLc
  have heA := edgeSupport_eq_component_erase F x y hxy A hAL hyA hAc hAu hAf hAi hisoA
  obtain ⟨S,hS,hyS,hsubS⟩ := high_edge_has_single_center_member F hu hf y hy x hxN
  obtain ⟨T,hT,hzT,hsubT⟩ := high_edge_has_single_center_member F hu hf z hz y hyNz
  have hSsubA : S ⊆ support A := by
    intro u huS
    rcases Finset.mem_insert.mp (hsubS huS) with rfl | huU
    · exact hyA
    · rw [edgeSupport_comm F y x,heA] at huU
      exact (Finset.mem_erase.mp huU).2
  have hxS : x ∉ S := by
    intro hxS
    obtain ⟨Q,hQA,hxQ⟩ := Finset.mem_biUnion.mp (hSsubA hxS)
    exact point_not_mem_residue F x Q (hAL hQA) hxQ
  have hU := high_edge_support_disjoint_high F hu hf y hy x hxN
  have hV := high_edge_support_disjoint_high F hu hf z hz y hyNz
  have hUV : Disjoint (edgeSupport F y x) (edgeSupport F z y) := by
    have h := incident_high_edge_supports_disjoint F hu hf y hy x z hxN hzN hxz
    rw [edgeSupport_comm F y z] at h
    exact h
  have hST : Disjoint S T :=
    (insert_centers_disjoint (highPoints F) _ _ y z hy hz hzy.symm hU hV hUV).mono hsubS hsubT
  have hxT : x ∉ T := by
    intro hxT
    rcases Finset.mem_insert.mp (hsubT hxT) with he | he
    · exact hxz he
    · exact Finset.disjoint_left.mp hV he hx
  let P := T \ {z}
  have hPz : P ∈ residualLink F {z} := mem_residualLink_iff.mpr ⟨T,hT,by simpa using hzT,rfl⟩
  have hP3 : P.card=3 := by simpa using (residualLink_uniform (core := ({z} : Finset α)) hu P hPz)
  have hPU : P ⊆ edgeSupport F z y := by
    intro u huP
    obtain ⟨huT,huz⟩ := Finset.mem_sdiff.mp huP
    rcases Finset.mem_insert.mp (hsubT huT) with he | he
    · exact False.elim (huz (by simp [he]))
    · exact he
  have hPD : P ∈ D := by
    apply (ten_three_point_transversal_iff_member D hDu hDf hDi hDc P hP3).mp
    intro Q hQD
    have hQL : Q ∈ residualLink F {x} := hDsub hQD
    have hR : insert x Q ∈ F := by simpa using core_union_residual_mem_family hQL
    have hSR : Disjoint S (insert x Q) := by
      apply Finset.disjoint_left.mpr
      intro u huS huR
      rcases Finset.mem_insert.mp huR with rfl | huQ
      · exact hxS huS
      · exact Finset.disjoint_left.mp hAD (hSsubA huS) (member_subset_support hQD huQ)
    have hmeet := disjoint_anchor_family_intersecting F S hS ⟨y,hyS⟩ hf (insert x Q)
      (Finset.mem_filter.mpr ⟨hR,Finset.disjoint_iff_inter_eq_empty.mp hSR.symm⟩) T
      (Finset.mem_filter.mpr ⟨hT,Finset.disjoint_iff_inter_eq_empty.mp hST.symm⟩)
      (Finset.insert_nonempty x Q) ⟨z,hzT⟩
    obtain ⟨u,hu⟩ := hmeet
    obtain ⟨huR,huT⟩ := Finset.mem_inter.mp hu
    rcases Finset.mem_insert.mp huR with rfl | huQ
    · exact False.elim (hxT huT)
    · have huz : u ≠ z := fun he => hzL (he ▸ member_subset_support hQL huQ)
      exact ⟨u,Finset.mem_inter.mpr ⟨huQ,Finset.mem_sdiff.mpr ⟨huT,by simpa using huz⟩⟩⟩
  have hPx : P ∈ residualLink F {x} := hDsub hPD
  have hPy := high_edge_single_residue_transfer F hu hf z hz y hyNz P hPz hPU
  exact no_three_common_point_residue F hf x y z hxy hxz hzy.symm P hPx hPy hPz

/-- The high-point adjacency graph has maximum degree one. -/
theorem high_point_high_neighbors_le_one {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (y : α) (hy : y ∈ highPoints F) : (highNeighbors F y).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx z hz
  by_contra hxz
  exact no_two_high_neighbors F hu hf y hy x z hx hz hxz

end Erdos20V10HighTriangle
