import SunflowerLean.Erdos20V10HighTriangleMain

namespace Erdos20V10HighTriangle
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20V8Boundary Erdos20DegreeCongruences Erdos20V9HighGraph
open Erdos20V9HighCompatibility Erdos20V5Frontier Erdos20V8Stability

/-- Every high edge has five residual support points. -/
theorem high_edge_support_card_five {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) (y : α) (hy : y ∈ highNeighbors F x) :
    (edgeSupport F x y).card=5 := by
  have hyx := ((mem_highNeighbors_iff F x y).mp hy).2.1
  obtain ⟨A,hAL,hyA,hAc,hAu,hAf,hAi,hiso⟩ := component_at_high_neighbor F hu hf x hx y hy
  rw [edgeSupport_eq_component_erase F x y hyx.symm A hAL hyA hAc hAu hAf hAi hiso,
    Finset.card_erase_of_mem hyA,(intersecting_ten_design A hAu hAf hAi hAc).1]

/-- The two high endpoints of an edge share every singleton residual supported
on that edge. This transfers an actual point-link block, not an encoded profile. -/
theorem high_edge_single_residue_transfer {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) (y : α) (hy : y ∈ highNeighbors F x)
    (P : Finset α) (hP : P ∈ residualLink F {x})
    (hPU : P ⊆ edgeSupport F x y) : P ∈ residualLink F {y} := by
  have hyH := ((mem_highNeighbors_iff F x y).mp hy).1
  have hyx := ((mem_highNeighbors_iff F x y).mp hy).2.1
  have hxN := high_neighbor_symm F x y hx hy
  obtain ⟨A,hAL,hyA,hAc,hAu,hAf,hAi,hisoA⟩ := component_at_high_neighbor F hu hf x hx y hy
  obtain ⟨B,hBL,hxB,hBc,hBu,hBf,hBi,hisoB⟩ := component_at_high_neighbor F hu hf y hyH x hxN
  have heA := edgeSupport_eq_component_erase F x y hyx.symm A hAL hyA hAc hAu hAf hAi hisoA
  have heB : edgeSupport F x y = (support B).erase x := by
    rw [edgeSupport_comm F x y]
    exact edgeSupport_eq_component_erase F y x hyx B hBL hxB hBc hBu hBf hBi hisoB
  have hP3 : P.card=3 := by
    have huL := residualLink_uniform (core := ({x} : Finset α)) hu
    simpa using huL P hP
  have hPA : P ∈ A := by
    obtain ⟨u,huP⟩ := Finset.card_pos.mp (show 0<P.card by omega)
    apply hisoA P hP
    refine ⟨u,Finset.mem_inter.mpr ⟨huP,?_⟩⟩
    have h := hPU huP
    rw [heA] at h
    exact (Finset.mem_erase.mp h).2
  have hyP : y ∉ P := by
    intro hyP
    have h := (mem_edgeSupport_iff F x y y).mp (hPU hyP)
    exact h.2.1 rfl
  apply hBL
  apply (ten_three_point_transversal_iff_member B hBu hBf hBi hBc P hP3).mp
  intro Q hQB
  by_cases hxQ : x ∈ Q
  · have hswap := switch_point_link F y x hyx Q (hBL hQB) hxQ
    have hQA := hisoA _ hswap ⟨y,Finset.mem_inter.mpr ⟨by simp,hyA⟩⟩
    obtain ⟨u,hu⟩ := hAi _ hQA P hPA
    obtain ⟨huQ,huP⟩ := Finset.mem_inter.mp hu
    rcases Finset.mem_insert.mp huQ with rfl | huQ
    · exact False.elim (hyP huP)
    · exact ⟨u,Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp huQ).2,huP⟩⟩
  · have hQU : Q ⊆ edgeSupport F x y := by
      intro u huQ
      rw [heB]
      exact Finset.mem_erase.mpr ⟨fun hux => hxQ (hux ▸ huQ),member_subset_support hQB huQ⟩
    have hU := high_edge_support_card_five F hu hf x hx y hy
    have hbound := Finset.card_le_card (Finset.union_subset hQU hPU)
    have hsum := Finset.card_union_add_card_inter Q P
    have hQ3 := hBu Q hQB
    apply Finset.card_pos.mp
    omega

end Erdos20V10HighTriangle
