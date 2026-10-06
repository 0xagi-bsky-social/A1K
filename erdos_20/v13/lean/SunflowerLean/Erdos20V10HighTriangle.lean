import SunflowerLean.Erdos20V9HighCompatibilityMain
import SunflowerLean.Erdos20V9HighGraph

namespace Erdos20V10HighTriangle
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20V8Boundary Erdos20DegreeCongruences Erdos20V9HighGraph
open Erdos20V9HighCompatibility Erdos20V9HighIncidence Erdos20V5Frontier

/-- The actual residual support of a two-point star. -/
def edgeSupport {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x y : α) : Finset α :=
  support (residualLink F {x,y})

theorem edgeSupport_comm {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (x y : α) : edgeSupport F x y = edgeSupport F y x := by
  simp only [edgeSupport,Finset.pair_comm]

theorem mem_edgeSupport_iff {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (x y u : α) :
    u ∈ edgeSupport F x y ↔ u ≠ x ∧ u ≠ y ∧ ∃ R ∈ F, x ∈ R ∧ y ∈ R ∧ u ∈ R := by
  constructor
  · intro h
    obtain ⟨P,hP,huP⟩ := Finset.mem_biUnion.mp h
    obtain ⟨R,hR,hxyR,hRP⟩ := mem_residualLink_iff.mp hP
    rw [← hRP] at huP
    obtain ⟨huR,hu⟩ := Finset.mem_sdiff.mp huP
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hu
    exact ⟨hu.1,hu.2,R,hR,hxyR (by simp),hxyR (by simp),huR⟩
  · rintro ⟨hux,huy,R,hR,hxR,hyR,huR⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨R \ {x,y},mem_residualLink_iff.mpr ⟨R,hR,?_,rfl⟩,?_⟩
    · simp [Finset.insert_subset_iff,hxR,hyR]
    · simp [huR,hux,huy]

/-- A supported neighbor selects an isolated ten-component of a high point link. -/
theorem component_at_high_neighbor {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) (y : α) (hy : y ∈ highNeighbors F x) :
    ∃ A ⊆ residualLink F {x}, y ∈ support A ∧ A.card=10 ∧
      (∀ P ∈ A, P.card=3) ∧ IsSunflowerFree A 3 ∧
      (∀ P ∈ A, ∀ Q ∈ A, (P ∩ Q).Nonempty) ∧
      (∀ Q ∈ residualLink F {x}, (Q ∩ support A).Nonempty → Q ∈ A) := by
  obtain ⟨P,hP,hyP⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hy).1
  obtain ⟨A,hAL,hPA,hAc,hAu,hAf,hAi,hiso⟩ :=
    high_point_component F hu hf x (Finset.mem_filter.mp hx).2 P hP
  exact ⟨A,hAL,member_subset_support hPA hyP,hAc,hAu,hAf,hAi,hiso⟩

/-- The support of an actual high-edge residue is the selected component support
with the neighboring center removed. -/
theorem edgeSupport_eq_component_erase {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (x y : α) (hxy : x ≠ y)
    (A : Finset (Finset α)) (hAL : A ⊆ residualLink F {x})
    (hyA : y ∈ support A) (hAc : A.card=10)
    (hAu : ∀ P ∈ A, P.card=3) (hAf : IsSunflowerFree A 3)
    (hAi : ∀ P ∈ A, ∀ Q ∈ A, (P ∩ Q).Nonempty)
    (hiso : ∀ Q ∈ residualLink F {x}, (Q ∩ support A).Nonempty → Q ∈ A) :
    edgeSupport F x y = (support A).erase y := by
  ext u
  constructor
  · intro hu
    obtain ⟨hux,huy,R,hR,hxR,hyR,huR⟩ := (mem_edgeSupport_iff F x y u).mp hu
    have hP : R \ {x} ∈ residualLink F {x} :=
      mem_residualLink_iff.mpr ⟨R,hR,by simpa using hxR,rfl⟩
    have hyP : y ∈ R \ {x} := by simp [hyR,hxy.symm]
    have hPA := hiso _ hP ⟨y,Finset.mem_inter.mpr ⟨hyP,hyA⟩⟩
    exact Finset.mem_erase.mpr ⟨huy,member_subset_support hPA (by simp [huR,hux])⟩
  · intro hu
    obtain ⟨huy,huA⟩ := Finset.mem_erase.mp hu
    have hp := (intersecting_ten_design A hAu hAf hAi hAc).2.2 u huA y hyA huy
    obtain ⟨P,hP⟩ := Finset.card_pos.mp (show 0 < (A.filter (fun P => ({u,y} : Finset α) ⊆ P)).card by omega)
    obtain ⟨hPA,huyP⟩ := Finset.mem_filter.mp hP
    obtain ⟨R,hR,hxR,hRP⟩ := mem_residualLink_iff.mp (hAL hPA)
    have huP := huyP (by simp : u ∈ ({u,y} : Finset α))
    have hyP := huyP (by simp : y ∈ ({u,y} : Finset α))
    rw [← hRP] at huP hyP
    obtain ⟨huR,hux⟩ := Finset.mem_sdiff.mp huP
    exact (mem_edgeSupport_iff F x y u).mpr
      ⟨by simpa using hux,huy,R,hR,Finset.singleton_subset_iff.mp hxR,(Finset.mem_sdiff.mp hyP).1,huR⟩

end Erdos20V10HighTriangle
