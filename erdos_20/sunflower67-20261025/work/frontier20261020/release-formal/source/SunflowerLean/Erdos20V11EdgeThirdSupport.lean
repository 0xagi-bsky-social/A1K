import SunflowerLean.Erdos20V11EdgeThirdDesign

namespace Erdos20V11EdgeThird
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20V8Boundary Erdos20DegreeCongruences Erdos20V9HighGraph
open Erdos20V10HighTriangle Erdos20V11HighSupport Erdos20V8HighWeights

/-- The matching theorem makes a third high point nonadjacent to both endpoints
of a high edge. -/
theorem third_high_nonadjacent_to_edge {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) (y : α) (hy : y ∈ highNeighbors F x)
    (z : α) (_hz : z ∈ highPoints F) (hxz : x ≠ z) (hyz : y ≠ z) :
    z ∉ highNeighbors F x ∧ z ∉ highNeighbors F y := by
  have hyH := ((mem_highNeighbors_iff F x y).mp hy).1
  have hxN := high_neighbor_symm F x y hx hy
  constructor
  · intro hzN
    exact hyz (Finset.card_le_one.mp (high_point_high_neighbors_le_one F hu hf x hx) y hy z hzN)
  · intro hzN
    exact hxz (Finset.card_le_one.mp (high_point_high_neighbors_le_one F hu hf y hyH) x hxN z hzN)

/-- A third high point's link support avoids the five-point residual support
of a high edge whenever the actual edge trace is restricted to zero or two. -/
theorem third_high_support_disjoint_of_edge_trace {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) (y : α) (hy : y ∈ highNeighbors F x)
    (ht : ∀ R ∈ F, x ∉ R → y ∉ R →
      (R ∩ edgeSupport F x y).card=0 ∨ (R ∩ edgeSupport F x y).card=2)
    (z : α) (hz : z ∈ highPoints F) (hxz : x ≠ z) (hyz : y ≠ z) :
    Disjoint (support (residualLink F {z})) (edgeSupport F x y) := by
  obtain ⟨hzNx,hzNy⟩ := third_high_nonadjacent_to_edge F hu hf x hx y hy z hz hxz hyz
  have hyH := ((mem_highNeighbors_iff F x y).mp hy).1
  have hxNz : x ∉ highNeighbors F z := fun hn => hzNx (high_neighbor_symm F z x hz hn)
  have hyNz : y ∉ highNeighbors F z := fun hn => hzNy (high_neighbor_symm F z y hz hn)
  have hxL := nonneighbor_not_mem_link_support F z x hx hxNz
  have hyL := nonneighbor_not_mem_link_support F z y hyH hyNz
  have hzU : z ∉ edgeSupport F x y := fun h =>
    Finset.disjoint_left.mp (high_edge_support_disjoint_high F hu hf x hx y hy) h hz
  have huL : ∀ P ∈ residualLink F {z}, P.card=3 := by
    simpa using residualLink_uniform (core := ({z} : Finset α)) hu
  apply twenty_zero_or_two_trace_support_disjoint _ huL (residualLink_sunflowerFree hf)
    (high_link_twenty_and_support_twelve F hu hf z hz).1
  intro P hP
  have hR : insert z P ∈ F := by simpa using core_union_residual_mem_family hP
  have hxR : x ∉ insert z P := by
    simp only [Finset.mem_insert,not_or]
    exact ⟨hxz,fun h => hxL (member_subset_support hP h)⟩
  have hyR : y ∉ insert z P := by
    simp only [Finset.mem_insert,not_or]
    exact ⟨hyz,fun h => hyL (member_subset_support hP h)⟩
  have he : insert z P ∩ edgeSupport F x y = P ∩ edgeSupport F x y := by
    ext u
    simp only [Finset.mem_inter,Finset.mem_insert]
    aesop
  simpa only [he] using ht (insert z P) hR hxR hyR

/-- Five residual edge points, twelve residual neighbors of a third high point,
and the three centers are disjoint supported sets. The edge trace premise is
explicit here and is discharged by the actual-family trace theorem downstream. -/
theorem twenty_le_support_of_edge_trace_and_third_high {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) (y : α) (hy : y ∈ highNeighbors F x)
    (ht : ∀ R ∈ F, x ∉ R → y ∉ R →
      (R ∩ edgeSupport F x y).card=0 ∨ (R ∩ edgeSupport F x y).card=2)
    (z : α) (hz : z ∈ highPoints F) (hxz : x ≠ z) (hyz : y ≠ z) :
    20 ≤ (support F).card := by
  let U := edgeSupport F x y
  let S := support (residualLink F {z})
  let C : Finset α := {x,y,z}
  have hdis := third_high_support_disjoint_of_edge_trace F hu hf x hx y hy ht z hz hxz hyz
  obtain ⟨hzNx,hzNy⟩ := third_high_nonadjacent_to_edge F hu hf x hx y hy z hz hxz hyz
  have hyH := ((mem_highNeighbors_iff F x y).mp hy).1
  have hxy : x ≠ y := ((mem_highNeighbors_iff F x y).mp hy).2.1.symm
  have hxNz : x ∉ highNeighbors F z := fun hn => hzNx (high_neighbor_symm F z x hz hn)
  have hyNz : y ∉ highNeighbors F z := fun hn => hzNy (high_neighbor_symm F z y hz hn)
  have hxS : x ∉ S := nonneighbor_not_mem_link_support F z x hx hxNz
  have hyS : y ∉ S := nonneighbor_not_mem_link_support F z y hyH hyNz
  have hzS : z ∉ S := by
    intro hm
    obtain ⟨P,hP,hzP⟩ := Finset.mem_biUnion.mp hm
    exact Erdos20V9HighCompatibility.point_not_mem_residue F z P hP hzP
  have hCH : C ⊆ highPoints F := by
    simp only [C,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    exact ⟨hx,hyH,hz⟩
  have hdUC : Disjoint U C := (high_edge_support_disjoint_high F hu hf x hx y hy).mono_right hCH
  have hdSC : Disjoint S C := by
    apply Finset.disjoint_right.mpr
    intro u huC huS
    simp only [C,Finset.mem_insert,Finset.mem_singleton] at huC
    rcases huC with rfl | rfl | rfl
    · exact hxS huS
    · exact hyS huS
    · exact hzS huS
  have hdUSC : Disjoint (U ∪ S) C := by
    apply Finset.disjoint_left.mpr
    intro u huUS huC
    rcases Finset.mem_union.mp huUS with huU | huS
    · exact Finset.disjoint_left.mp hdUC huU huC
    · exact Finset.disjoint_left.mp hdSC huS huC
  have hU5 : U.card=5 := high_edge_support_card_five F hu hf x hx y hy
  have hS12 : S.card=12 := (high_link_twenty_and_support_twelve F hu hf z hz).2
  have hC3 : C.card=3 := by simp [C,hxy,hxz,hyz]
  have hcard : ((U ∪ S) ∪ C).card=20 := by
    rw [Finset.card_union_of_disjoint hdUSC,Finset.card_union_of_disjoint hdis.symm,hU5,hS12,hC3]
  have hsub : (U ∪ S) ∪ C ⊆ support F := by
    apply Finset.union_subset
    · exact Finset.union_subset (residual_support_subset F {x,y}) (residual_support_subset F {z})
    · exact hCH.trans (Finset.filter_subset _ _)
  have hb := Finset.card_le_card hsub
  omega

end Erdos20V11EdgeThird
