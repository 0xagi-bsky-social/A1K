import SunflowerLean.Erdos20V10HighTriangleDegreeOne

namespace Erdos20V11EdgeTrace
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20V8Boundary Erdos20V9HighGraph Erdos20V10HighTriangle Erdos20DesignNormalForm
open Erdos20V9HighCompatibility Erdos20V5Frontier Erdos20RankThree

/-- A kernel-evaluated certificate for all traces on a vertex-deleted
canonical ten-design. Equal pairwise intersections give the forbidden core. -/
theorem canonical_deleted_trace_certificate :
    ∀ (a : Fin 6) (T : Finset (Fin 6)), a ∉ T → T.card ≠ 0 → T.card ≠ 2 →
    ∃ P ∈ canonicalTen (0 : Fin 6) 1 2 3 4 5,
    ∃ Q ∈ canonicalTen (0 : Fin 6) 1 2 3 4 5,
      a ∉ P ∧ a ∉ Q ∧ P ∩ T = P ∩ Q ∧ Q ∩ T = P ∩ Q := by
  decide +kernel

/-- Semantic bridge from equal traces to three distinct original petals. -/
theorem shared_trace_forbidden {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hf : IsSunflowerFree F 3)
    (x y : α) (hxy : x ≠ y) (P Q R : Finset α)
    (hPx : x ∉ P) (hPy : y ∉ P) (hQx : x ∉ Q) (hQy : y ∉ Q)
    (hRx : x ∉ R) (hRy : y ∉ R)
    (hP : insert x P ∈ F) (hQ : insert y Q ∈ F) (hR : R ∈ F)
    (hPR : P ∩ R = P ∩ Q) (hQR : Q ∩ R = P ∩ Q) : False := by
  have hn1 : insert x P ≠ insert y Q := by
    intro he
    have hm : x ∈ insert y Q := he ▸ Finset.mem_insert_self x P
    simp [hxy,hQx] at hm
  have hn2 : insert x P ≠ R := by
    intro he
    exact hRx (he ▸ Finset.mem_insert_self x P)
  have hn3 : insert y Q ≠ R := by
    intro he
    exact hRy (he ▸ Finset.mem_insert_self y Q)
  apply hf {insert x P,insert y Q,R}
  · intro S hS
    simp only [Finset.mem_insert,Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl <;> assumption
  · apply sunflower_three_of_intersections _ _ _ (P ∩ Q) hn1 hn2 hn3
    · ext u
      simp only [Finset.mem_inter,Finset.mem_insert]
      aesop
    · rw [← hPR]
      ext u
      simp only [Finset.mem_inter,Finset.mem_insert]
      aesop
    · rw [← hQR]
      ext u
      simp only [Finset.mem_inter,Finset.mem_insert]
      aesop

/-- Images transport a trace from finite coordinates to the original universe. -/
theorem image_trace {α : Type*} [DecidableEq α] (e : Fin 6 ↪ α)
    (P : Finset (Fin 6)) (R : Finset α) :
    P.image e ∩ R = (P ∩ Finset.univ.filter (fun i => e i ∈ R)).image e := by
  ext u
  simp only [Finset.mem_inter,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨i,hi,rfl⟩,hr⟩
    exact ⟨i,⟨hi,hr⟩,rfl⟩
  · rintro ⟨i,⟨hi,hr⟩,rfl⟩
    exact ⟨⟨i,hi,rfl⟩,hr⟩


/-- A member avoiding both endpoints of a high edge meets its five-point
residual support in zero or two points. -/
theorem high_edge_member_trace_zero_or_two {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) (y : α) (hy : y ∈ highNeighbors F x)
    (R : Finset α) (hR : R ∈ F) (hxR : x ∉ R) (hyR : y ∉ R) :
    (R ∩ edgeSupport F x y).card=0 ∨ (R ∩ edgeSupport F x y).card=2 := by
  classical
  have hxy : x ≠ y := ((mem_highNeighbors_iff F x y).mp hy).2.1.symm
  obtain ⟨A,hAL,hyA,hAc,hAu,hAf,hAi,hiso⟩ := component_at_high_neighbor F hu hf x hx y hy
  have heU := edgeSupport_eq_component_erase F x y hxy A hAL hyA hAc hAu hAf hAi hiso
  obtain ⟨e,he⟩ := ten_isomorphic_canonical A hAu hAf hAi hAc
  have hAS : support A ⊆ Finset.univ.image e := by
    intro u huA
    obtain ⟨P,hP,huP⟩ := Finset.mem_biUnion.mp huA
    rw [he] at hP
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp huP
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
  have heS : support A = Finset.univ.image e := by
    apply Finset.eq_of_subset_of_card_le hAS
    rw [Finset.card_image_of_injective _ e.injective,
      (intersecting_ten_design A hAu hAf hAi hAc).1]
    decide
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (hAS hyA)
  let T : Finset (Fin 6) := Finset.univ.filter (fun i => e i ∈ R)
  have haT : a ∉ T := by simpa [T] using hyR
  have htrace : R ∩ edgeSupport F x (e a) = T.image e := by
    rw [heU,heS]
    ext u
    simp only [Finset.mem_inter,Finset.mem_erase,Finset.mem_image,
      Finset.mem_univ,true_and,T,Finset.mem_filter]
    constructor
    · rintro ⟨huR,hua,i,rfl⟩
      exact ⟨i,huR,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      refine ⟨hi,?_,i,rfl⟩
      intro hie
      exact hyR (hie ▸ hi)
  have hcard : (R ∩ edgeSupport F x (e a)).card = T.card := by
    rw [htrace,Finset.card_image_of_injective _ e.injective]
  rw [hcard]
  by_contra hn
  have h0 : T.card ≠ 0 := fun h => hn (Or.inl h)
  have h2 : T.card ≠ 2 := fun h => hn (Or.inr h)
  obtain ⟨P,hP,Q,hQ,haP,haQ,hPT,hQT⟩ := canonical_deleted_trace_certificate a T haT h0 h2
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
  apply shared_trace_forbidden F hf x (e a) hxy (P.image e) (Q.image e) R
    hxP hyP hxQ hyQ hxR hyR hPf hQf hR
  · rw [image_trace,show Finset.univ.filter (fun i => e i ∈ R) = T from rfl,hPT]
    exact Finset.image_inter P Q e.injective
  · rw [image_trace,show Finset.univ.filter (fun i => e i ∈ R) = T from rfl,hQT]
    exact Finset.image_inter P Q e.injective

end Erdos20V11EdgeTrace
