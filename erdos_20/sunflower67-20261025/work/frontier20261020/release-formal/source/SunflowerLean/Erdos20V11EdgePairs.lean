import SunflowerLean.Erdos20V11EdgeTrace

namespace Erdos20V11EdgePairs
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence Erdos20V8Boundary
open Erdos20V9HighGraph Erdos20V10HighTriangle Erdos20DesignNormalForm
open Erdos20V9HighCompatibility Erdos20V5Frontier Erdos20V11EdgeTrace

def D : Finset (Finset (Fin 6)) := canonicalTen 0 1 2 3 4 5

/-- The five cycle pairs of a deleted canonical design, restricted to
those containing the specified point. -/
def allowedPairs (a b : Fin 6) : Finset (Finset (Fin 6)) :=
  Finset.univ.filter (fun C => C.card=2 ∧ a ∉ C ∧ b ∈ C ∧ insert a C ∈ D)

theorem allowedPairs_card : ∀ a b : Fin 6, a ≠ b → (allowedPairs a b).card=2 := by
  decide +kernel

/-- Each admissible pair lies in a block avoiding the deleted point. -/
theorem allowedPairs_avoiding_block : ∀ (a b : Fin 6) (C : Finset (Fin 6)),
    C ∈ allowedPairs a b →
    ∃ P ∈ D, a ∉ P ∧ C ⊆ P := by
  decide +kernel

theorem canonical_noncycle_trace_certificate :
    ∀ (a : Fin 6) (T : Finset (Fin 6)), a ∉ T → T.card=2 → insert a T ∉ D →
    ∃ P ∈ D, ∃ Q ∈ D,
      a ∉ P ∧ a ∉ Q ∧ P ∩ T = P ∩ Q ∧ Q ∩ T = P ∩ Q := by
  decide +kernel

/-- The prohibited noncycle trace is ruled out in the actual original family. -/
theorem original_trace_is_cycle_of_card_two {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) (y : α) (hy : y ∈ highNeighbors F x)
    (A : Finset (Finset α)) (hAL : A ⊆ residualLink F {x})
    (heU : edgeSupport F x y = (support A).erase y)
    (e : Fin 6 ↪ α) (he : A = D.image (fun P => P.image e))
    (a : Fin 6) (ha : e a = y)
    (R : Finset α) (hR : R ∈ F) (hxR : x ∉ R) (hyR : y ∉ R)
    (hT2 : (Finset.univ.filter (fun i => e i ∈ R)).card=2) :
    insert a (Finset.univ.filter (fun i => e i ∈ R)) ∈ D := by
  classical
  subst y
  let T : Finset (Fin 6) := Finset.univ.filter (fun i => e i ∈ R)
  have haT : a ∉ T := by simpa [T] using hyR
  by_contra hcycle
  obtain ⟨P,hP,Q,hQ,haP,haQ,hPT,hQT⟩ := canonical_noncycle_trace_certificate a T haT hT2 hcycle
  have hPA : P.image e ∈ A := by rw [he]; exact Finset.mem_image.mpr ⟨P,hP,rfl⟩
  have hQA : Q.image e ∈ A := by rw [he]; exact Finset.mem_image.mpr ⟨Q,hQ,rfl⟩
  have hyP : e a ∉ P.image e := by simpa using haP
  have hyQ : e a ∉ Q.image e := by simpa using haQ
  have hxP := point_not_mem_residue F x _ (hAL hPA)
  have hxQ := point_not_mem_residue F x _ (hAL hQA)
  have hQU : Q.image e ⊆ edgeSupport F x (e a) := by
    rw [heU]
    intro u huQ
    exact Finset.mem_erase.mpr ⟨fun hua => hyQ (hua ▸ huQ),member_subset_support hQA huQ⟩
  have hQy := high_edge_single_residue_transfer F hu hf x hx (e a) hy _ (hAL hQA) hQU
  have hPf : insert x (P.image e) ∈ F := by simpa using core_union_residual_mem_family (hAL hPA)
  have hQf : insert (e a) (Q.image e) ∈ F := by simpa using core_union_residual_mem_family hQy
  have hxy : x ≠ e a := ((mem_highNeighbors_iff F x (e a)).mp hy).2.1.symm
  apply shared_trace_forbidden F hf x (e a) hxy (P.image e) (Q.image e) R
    hxP hyP hxQ hyQ hxR hyR hPf hQf hR
  · rw [image_trace,show Finset.univ.filter (fun i => e i ∈ R) = T from rfl,hPT]
    exact Finset.image_inter P Q e.injective
  · rw [image_trace,show Finset.univ.filter (fun i => e i ∈ R) = T from rfl,hQT]
    exact Finset.image_inter P Q e.injective

end Erdos20V11EdgePairs
