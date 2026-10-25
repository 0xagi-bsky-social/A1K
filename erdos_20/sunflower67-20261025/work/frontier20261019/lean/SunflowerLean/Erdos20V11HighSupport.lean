import SunflowerLean.Erdos20V10HighTriangleIncidence
import SunflowerLean.Erdos20ExtremalTransversals

namespace Erdos20V11HighSupport
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence Erdos20RankThree
open Erdos20V8Boundary Erdos20DegreeCongruences Erdos20V9HighGraph
open Erdos20V10HighTriangle Erdos20ExtremalTransversals Erdos20ExtremalTwenty

/-- Every six-point transversal of an extremal triple family is contained in
its actual support. No precomputed classification of a labelled design is used. -/
theorem twenty_transversal_six_subset_support {α : Type*} [DecidableEq α]
    (L : Finset (Finset α)) (hu : ∀ P ∈ L, P.card=3)
    (hf : IsSunflowerFree L 3) (hc : L.card=20)
    (C : Finset α) (hC : C.card=6)
    (hhit : ∀ P ∈ L, (P ∩ C).Nonempty) : C ⊆ support L := by
  have hmin := extremal_twenty_transversal_card_ge_six L hu hf hc
    (C ∩ support L) (transversal_restrict_support L L C (Finset.Subset.refl _) hhit)
  have he : C ∩ support L = C := Finset.eq_of_subset_of_card_le
    Finset.inter_subset_left (by omega)
  intro u huC
  have hu := he.symm ▸ huC
  exact (Finset.mem_inter.mp hu).2

/-- A high point's link has twenty triples and twelve supported points. -/
theorem high_link_twenty_and_support_twelve {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) :
    (residualLink F {x}).card=20 ∧ (support (residualLink F {x})).card=12 := by
  have hLu : ∀ P ∈ residualLink F {x}, P.card=3 := by
    simpa using residualLink_uniform (core := ({x} : Finset α)) hu
  have hc : (residualLink F {x}).card=20 := by
    simpa [card_residualLink,upperStar,degree] using (Finset.mem_filter.mp hx).2
  exact ⟨hc,(extremal_twenty_regular_twelve _ hLu (residualLink_sunflowerFree hf) hc).1⟩

/-- A high point absent from another high point's neighbor set is absent from
its whole residual support. -/
theorem nonneighbor_not_mem_link_support {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (x y : α) (hy : y ∈ highPoints F)
    (hxy : y ∉ highNeighbors F x) : y ∉ support (residualLink F {x}) := by
  intro hyL
  exact hxy (Finset.mem_inter.mpr ⟨hyL,hy⟩)

/-- Three pairwise nonadjacent high centers force each residue at the first
center to be supported in the third center's link. This is an actual-family
bridge using the prohibition of three disjoint original members. -/
theorem residue_subset_third_high_support {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x y z : α) (hx : x ∈ highPoints F) (hy : y ∈ highPoints F)
    (hz : z ∈ highPoints F) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hyNx : y ∉ highNeighbors F x) (hzNx : z ∉ highNeighbors F x)
    (hzNy : z ∉ highNeighbors F y)
    (R : Finset α) (hR : R ∈ residualLink F {x}) :
    R ⊆ support (residualLink F {z}) := by
  classical
  have hxNy : x ∉ highNeighbors F y := fun hn => hyNx (high_neighbor_symm F y x hy hn)
  have hxNz : x ∉ highNeighbors F z := fun hn => hzNx (high_neighbor_symm F z x hz hn)
  have hyNz : y ∉ highNeighbors F z := fun hn => hzNy (high_neighbor_symm F z y hz hn)
  have hyLx := nonneighbor_not_mem_link_support F x y hy hyNx
  have hzLx := nonneighbor_not_mem_link_support F x z hz hzNx
  have hxLy := nonneighbor_not_mem_link_support F y x hx hxNy
  have hzLy := nonneighbor_not_mem_link_support F y z hz hzNy
  have hxLz := nonneighbor_not_mem_link_support F z x hx hxNz
  have hyLz := nonneighbor_not_mem_link_support F z y hy hyNz
  have huY : ∀ P ∈ residualLink F {y}, P.card=3 := by
    simpa using residualLink_uniform (core := ({y} : Finset α)) hu
  have huZ : ∀ P ∈ residualLink F {z}, P.card=3 := by
    simpa using residualLink_uniform (core := ({z} : Finset α)) hu
  have hR3 : R.card=3 := by
    simpa using residualLink_uniform (core := ({x} : Finset α)) hu R hR
  obtain ⟨S,hS,hSR⟩ := extremal_twenty_avoids_five_points _ huY
    (residualLink_sunflowerFree hf) (high_link_twenty_and_support_twelve F hu hf y hy).1 R (by omega)
  have hRF : insert x R ∈ F := by simpa using core_union_residual_mem_family hR
  have hSF : insert y S ∈ F := by simpa using core_union_residual_mem_family hS
  have hRS : Disjoint R S := (Finset.disjoint_iff_inter_eq_empty.mpr hSR).symm
  have hRSF : Disjoint (insert x R) (insert y S) := by
    apply Finset.disjoint_left.mpr
    intro u huR huS
    rcases Finset.mem_insert.mp huR with rfl | huR
    · rcases Finset.mem_insert.mp huS with he | huS
      · exact hxy he
      · exact hxLy (member_subset_support hS huS)
    · rcases Finset.mem_insert.mp huS with rfl | huS
      · exact hyLx (member_subset_support hR huR)
      · exact Finset.disjoint_left.mp hRS huR huS
  have hhit : ∀ P ∈ residualLink F {z}, (P ∩ (R ∪ S)).Nonempty := by
    intro P hP
    have hPF : insert z P ∈ F := by simpa using core_union_residual_mem_family hP
    by_contra hn
    have hdPR : Disjoint (insert z P) (insert x R) := by
      apply Finset.disjoint_left.mpr
      intro u huP huR
      rcases Finset.mem_insert.mp huP with rfl | huP
      · rcases Finset.mem_insert.mp huR with he | huR
        · exact hxz he.symm
        · exact hzLx (member_subset_support hR huR)
      · rcases Finset.mem_insert.mp huR with rfl | huR
        · exact hxLz (member_subset_support hP huP)
        · exact hn ⟨u,Finset.mem_inter.mpr ⟨huP,Finset.mem_union_left _ huR⟩⟩
    have hdPS : Disjoint (insert z P) (insert y S) := by
      apply Finset.disjoint_left.mpr
      intro u huP huS
      rcases Finset.mem_insert.mp huP with rfl | huP
      · rcases Finset.mem_insert.mp huS with he | huS
        · exact hyz he.symm
        · exact hzLy (member_subset_support hS huS)
      · rcases Finset.mem_insert.mp huS with rfl | huS
        · exact hyLz (member_subset_support hP huP)
        · exact hn ⟨u,Finset.mem_inter.mpr ⟨huP,Finset.mem_union_right _ huS⟩⟩
    have hm := disjoint_anchor_family_intersecting F (insert z P) hPF
      (Finset.insert_nonempty z P) hf (insert x R)
      (Finset.mem_filter.mpr ⟨hRF,Finset.disjoint_iff_inter_eq_empty.mp hdPR.symm⟩)
      (insert y S) (Finset.mem_filter.mpr ⟨hSF,Finset.disjoint_iff_inter_eq_empty.mp hdPS.symm⟩)
      (Finset.insert_nonempty x R) (Finset.insert_nonempty y S)
    rw [Finset.disjoint_iff_inter_eq_empty.mp hRSF] at hm
    exact Finset.not_nonempty_empty hm
  have hC6 : (R ∪ S).card=6 := by
    rw [Finset.card_union_of_disjoint hRS,hR3,huY S hS]
  exact Finset.Subset.trans Finset.subset_union_left
    (twenty_transversal_six_subset_support _ huZ (residualLink_sunflowerFree hf)
      (high_link_twenty_and_support_twelve F hu hf z hz).1 _ hC6 hhit)

/-- Pairwise nonadjacent high triples share one twelve-point residual support. -/
theorem three_nonadjacent_high_supports_eq {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x y z : α) (hx : x ∈ highPoints F) (hy : y ∈ highPoints F)
    (hz : z ∈ highPoints F) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hyNx : y ∉ highNeighbors F x) (hzNx : z ∉ highNeighbors F x)
    (hzNy : z ∉ highNeighbors F y) :
    support (residualLink F {x}) = support (residualLink F {z}) ∧
    support (residualLink F {y}) = support (residualLink F {z}) := by
  have hxNy : x ∉ highNeighbors F y := fun hn => hyNx (high_neighbor_symm F y x hy hn)
  have hsubX : support (residualLink F {x}) ⊆ support (residualLink F {z}) := by
    intro u huS
    obtain ⟨R,hR,huR⟩ := Finset.mem_biUnion.mp huS
    exact residue_subset_third_high_support F hu hf x y z hx hy hz hxy hxz hyz hyNx hzNx hzNy R hR huR
  have hsubY : support (residualLink F {y}) ⊆ support (residualLink F {z}) := by
    intro u huS
    obtain ⟨R,hR,huR⟩ := Finset.mem_biUnion.mp huS
    exact residue_subset_third_high_support F hu hf y x z hy hx hz hxy.symm hyz hxz hxNy hzNy hzNx R hR huR
  have hcX := (high_link_twenty_and_support_twelve F hu hf x hx).2
  have hcY := (high_link_twenty_and_support_twelve F hu hf y hy).2
  have hcZ := (high_link_twenty_and_support_twelve F hu hf z hz).2
  exact ⟨Finset.eq_of_subset_of_card_le hsubX (by omega),Finset.eq_of_subset_of_card_le hsubY (by omega)⟩

end Erdos20V11HighSupport
