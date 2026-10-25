import SunflowerLean.Erdos20V11DegreeSeventeenLink

namespace Erdos20V11DegreeSeventeen
open Erdos20BCWConditional Erdos20StrictCore Erdos20RankThree
open Erdos20DegreeCongruences Erdos20V8Global

/-- For separated supports, the disjoint neighborhood of a member of an
intersecting component is exactly the other component. -/
theorem exact_disjoint_trace_of_separated_partition
    {α : Type*} [DecidableEq α] (F A B : Finset (Finset α))
    (hF : F = A ∪ B) (hsep : Disjoint (support A) (support B))
    (hiA : ∀ S ∈ A, ∀ T ∈ A, (S ∩ T).Nonempty)
    (S : Finset α) (hS : S ∈ A) : exactTrace F S ∅ = B := by
  classical
  ext T
  change T ∈ F.filter (fun T => T ∩ S = ∅) ↔ T ∈ B
  constructor
  · intro hT
    obtain ⟨hTF,hTS⟩ := Finset.mem_filter.mp hT
    rw [hF] at hTF
    rcases Finset.mem_union.mp hTF with hTA | hTB
    · have hn := hiA T hTA S hS
      simp [hTS] at hn
    · exact hTB
  · intro hTB
    apply Finset.mem_filter.mpr
    refine ⟨?_,?_⟩
    · rw [hF]
      exact Finset.mem_union_right _ hTB
    · apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hxT,hxS⟩ := Finset.mem_inter.mp hx
      exact Finset.disjoint_left.mp hsep
        (Finset.mem_biUnion.mpr ⟨S,hS,hxS⟩)
        (Finset.mem_biUnion.mpr ⟨T,hTB,hxT⟩)

/-- The seventeen-member case has exactly eight members of disjoint degree
nine and nine members of disjoint degree eight. -/
theorem triple_seventeen_exact_disjoint_degree_distribution
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hc : F.card = 17) (hd : ∀ S ∈ F, 8 ≤ (exactTrace F S ∅).card) :
    (∀ S ∈ F, (exactTrace F S ∅).card = 8 ∨ (exactTrace F S ∅).card = 9) ∧
    (F.filter (fun S => (exactTrace F S ∅).card = 9)).card = 8 ∧
    (F.filter (fun S => (exactTrace F S ∅).card = 8)).card = 9 := by
  classical
  obtain ⟨A,B,hF,hA,hB,hsep,hiA,hiB⟩ :=
    triple_seventeen_min_disjoint_eight_decomposition F hu hf hc hd
  have hDA : ∀ S ∈ A, (exactTrace F S ∅).card = 9 := by
    intro S hS
    rw [exact_disjoint_trace_of_separated_partition F A B hF hsep hiA S hS,hB]
  have hDB : ∀ S ∈ B, (exactTrace F S ∅).card = 8 := by
    intro S hS
    rw [exact_disjoint_trace_of_separated_partition F B A
      (by simpa [Finset.union_comm] using hF) hsep.symm hiB S hS,hA]
  have h9 : F.filter (fun S => (exactTrace F S ∅).card = 9) = A := by
    ext S
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hSF,hdS⟩
      rw [hF] at hSF
      rcases Finset.mem_union.mp hSF with hSA | hSB
      · exact hSA
      · have hdB := hDB S hSB
        omega
    · intro hSA
      exact ⟨by rw [hF]; exact Finset.mem_union_left _ hSA,hDA S hSA⟩
  have h8 : F.filter (fun S => (exactTrace F S ∅).card = 8) = B := by
    ext S
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hSF,hdS⟩
      rw [hF] at hSF
      rcases Finset.mem_union.mp hSF with hSA | hSB
      · have hdA := hDA S hSA
        omega
      · exact hSB
    · intro hSB
      exact ⟨by rw [hF]; exact Finset.mem_union_right _ hSB,hDB S hSB⟩
  refine ⟨?_,by rw [h9,hA],by rw [h8,hB]⟩
  intro S hS
  rw [hF] at hS
  rcases Finset.mem_union.mp hS with hSA | hSB
  · exact Or.inr (hDA S hSA)
  · exact Or.inl (hDB S hSB)

/-- Every singleton trace at a degree-seventeen point is exactly eight or
nine, provided all original members meet at least fifty-four members. -/
theorem degree_seventeen_singleton_trace_eight_or_nine
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (hm : ∀ R ∈ F, 54 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card)
    (x : α) (hx : degree F x = 17) (R : Finset α) (hR : R ∈ F) (hxR : x ∈ R) :
    (exactTrace F R {x}).card = 8 ∨ (exactTrace F R {x}).card = 9 := by
  have hdist := triple_seventeen_exact_disjoint_degree_distribution (residualLink F {x})
    (by simpa using residualLink_uniform (core := {x}) hu)
    (residualLink_sunflowerFree hf)
    (by simpa [card_residualLink,upperStar,degree] using hx)
    (degree_seventeen_link_min_disjoint_eight F hu hf hm x hx)
  have hmem : R \ {x} ∈ residualLink F {x} :=
    mem_residualLink_iff.mpr ⟨R,hR,by simpa,rfl⟩
  have hD := hdist.1 (R \ {x}) hmem
  rw [← singleton_residual_eq_empty_link_trace F R x hxR,exact_trace_card_residual] at hD
  exact hD

end Erdos20V11DegreeSeventeen
