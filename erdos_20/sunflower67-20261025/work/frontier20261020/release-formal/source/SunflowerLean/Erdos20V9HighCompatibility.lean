import SunflowerLean.Erdos20V8HighWeights

namespace Erdos20V9HighCompatibility
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20ExtremalTwenty Erdos20DesignNormalForm Erdos20V8Boundary
open Erdos20DegreeCongruences

/-- A selected member of an extremal triple family lies in an isolated ten-design. -/
theorem twenty_component_at_member
    {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hu : ∀ P ∈ L, P.card = 3) (hf : IsSunflowerFree L 3) (hc : L.card = 20)
    (P : Finset α) (hP : P ∈ L) :
    ∃ H ⊆ L, P ∈ H ∧ H.card = 10 ∧
      (∀ A ∈ H, ∀ B ∈ H, (A ∩ B).Nonempty) ∧
      (∀ Q ∈ L, (Q ∩ support H).Nonempty → Q ∈ H) := by
  classical
  obtain ⟨H,K,hL,hdis,hpars⟩ := extremal_twenty_two_disjoint_designs L hu hf hc
  have hh := hpars H (by simp)
  have hk := hpars K (by simp)
  have hHsub : H ⊆ L := by rw [hL]; exact Finset.subset_union_left
  have hKsub : K ⊆ L := by rw [hL]; exact Finset.subset_union_right
  rw [hL] at hP
  rcases Finset.mem_union.mp hP with hP | hP
  · refine ⟨H,hHsub,hP,hh.1,hh.2.1,?_⟩
    intro Q hQ hmeet
    rw [hL] at hQ
    rcases Finset.mem_union.mp hQ with hQ | hQ
    · exact hQ
    · obtain ⟨z,hz⟩ := hmeet
      obtain ⟨hzQ,hzH⟩ := Finset.mem_inter.mp hz
      exact False.elim (Finset.disjoint_left.mp hdis hzH (member_subset_support hQ hzQ))
  · refine ⟨K,hKsub,hP,hk.1,hk.2.1,?_⟩
    intro Q hQ hmeet
    rw [hL] at hQ
    rcases Finset.mem_union.mp hQ with hQ | hQ
    · obtain ⟨z,hz⟩ := hmeet
      obtain ⟨hzQ,hzK⟩ := Finset.mem_inter.mp hz
      exact False.elim (Finset.disjoint_left.mp hdis (member_subset_support hQ hzQ) hzK)
    · exact hQ

/-- Every point-link residue avoids the removed point. -/
theorem point_not_mem_residue
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x : α)
    (P : Finset α) (hP : P ∈ residualLink F {x}) : x ∉ P := by
  obtain ⟨S,_,_,rfl⟩ := mem_residualLink_iff.mp hP
  simp

/-- A two-point incidence may be viewed from either point link. -/
theorem switch_point_link
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x y : α) (hxy : x ≠ y)
    (P : Finset α) (hP : P ∈ residualLink F {x}) (hy : y ∈ P) :
    insert x (P.erase y) ∈ residualLink F {y} := by
  obtain ⟨S,hS,hxS,hSP⟩ := mem_residualLink_iff.mp hP
  have hx : x ∈ S := Finset.singleton_subset_iff.mp hxS
  have hyS : y ∈ S := by rw [← hSP] at hy; exact (Finset.mem_sdiff.mp hy).1
  apply mem_residualLink_iff.mpr
  refine ⟨S,hS,Finset.singleton_subset_iff.mpr hyS,?_⟩
  rw [← hSP]
  ext z
  simp only [Finset.mem_sdiff,Finset.mem_singleton,Finset.mem_insert,Finset.mem_erase]
  by_cases hzx : z=x
  · subst z
    simp [hx,hxy]
  · simp [hzx]
    tauto

/-- Switching a displayed triple between point links. -/
theorem switch_triple_link
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (x y a b : α) (hxy : x ≠ y) (hya : y ≠ a) (hyb : y ≠ b)
    (hP : {y,a,b} ∈ residualLink F {x}) :
    {x,a,b} ∈ residualLink F {y} := by
  simpa [hya,hyb] using switch_point_link F x y hxy {y,a,b} hP (by simp)

/-- A point-link triple recovered from an original four-element member. -/
theorem triple_link_of_four_member
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (x y z w : α) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hR : {x,y,z,w} ∈ F) : {y,z,w} ∈ residualLink F {x} := by
  apply mem_residualLink_iff.mpr
  refine ⟨{x,y,z,w},hR,by simp,?_⟩
  ext t
  simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | ht | ht | ht,hn⟩
    · exact False.elim (hn rfl)
    · exact Or.inl ht
    · exact Or.inr (Or.inl ht)
    · exact Or.inr (Or.inr ht)
  · rintro (rfl | rfl | rfl) <;> simp_all [eq_comm]

end Erdos20V9HighCompatibility
