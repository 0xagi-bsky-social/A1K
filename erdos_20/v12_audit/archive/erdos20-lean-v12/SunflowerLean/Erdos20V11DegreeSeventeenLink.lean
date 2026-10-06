import SunflowerLean.Erdos20V11DegreeSeventeen
import SunflowerLean.Erdos20V10MinimumDegree

namespace Erdos20V11DegreeSeventeen
open Erdos20BCWConditional Erdos20StrictCore Erdos20RankThree
open Erdos20DegreeCongruences Erdos20V8Global Erdos20V10Profile54Bridge

/-- A degree-seventeen point in a family with all meeting neighborhoods at
least fifty-four has at least eight disjoint partners per member of its link. -/
theorem degree_seventeen_link_min_disjoint_eight
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (hm : ∀ R ∈ F, 54 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card)
    (x : α) (hx : degree F x = 17) :
    ∀ A ∈ residualLink F {x},
      8 ≤ (exactTrace (residualLink F {x}) A ∅).card := by
  classical
  intro A hA
  obtain ⟨S,hS,hxS,hSA⟩ := mem_residualLink_iff.mp hA
  have hxS' : x ∈ S := hxS (by simp)
  have hscore := meeting_at_least_fifty_four_degree_trace_score F hu hf S hS
    (hm S hS) x hxS'
  have he : (exactTrace (residualLink F {x}) A ∅).card =
      (exactTrace F S {x}).card := by
    rw [← hSA]
    rw [← singleton_residual_eq_empty_link_trace F S x hxS',exact_trace_card_residual]
  rw [he]
  omega

/-- The actual residual link of a degree-seventeen point is the disjoint-support
union of an intersecting eight-member family and an intersecting nine-member
family. This bridge has only the original four-uniform family hypotheses. -/
theorem degree_seventeen_link_eight_nine_decomposition
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (hm : ∀ R ∈ F, 54 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card)
    (x : α) (hx : degree F x = 17) :
    ∃ A B : Finset (Finset α), residualLink F {x} = A ∪ B ∧
      A.card = 8 ∧ B.card = 9 ∧ Disjoint (support A) (support B) ∧
      (∀ S ∈ A, ∀ T ∈ A, (S ∩ T).Nonempty) ∧
      (∀ S ∈ B, ∀ T ∈ B, (S ∩ T).Nonempty) := by
  apply triple_seventeen_min_disjoint_eight_decomposition
  · simpa using residualLink_uniform (core := {x}) hu
  · exact residualLink_sunflowerFree hf
  · simpa [card_residualLink,upperStar,degree] using hx
  · exact degree_seventeen_link_min_disjoint_eight F hu hf hm x hx

/-- In the separated eight/nine case, every point of the triple family occurs
at most five times. -/
theorem triple_seventeen_min_disjoint_eight_degree_le_five
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hc : F.card = 17)
    (hd : ∀ S ∈ F, 8 ≤ (exactTrace F S ∅).card) (x : α) :
    (F.filter (fun S => x ∈ S)).card ≤ 5 := by
  classical
  obtain ⟨A,B,hF,hA,hB,hsep,hiA,hiB⟩ :=
    triple_seventeen_min_disjoint_eight_decomposition F hu hf hc hd
  have hAF : A ⊆ F := by rw [hF]; exact Finset.subset_union_left
  have hBF : B ⊆ F := by rw [hF]; exact Finset.subset_union_right
  have hAcap := Erdos20ExtremalStructure.intersecting_card_ge_seven_degree_le_five A
    (fun S hS => hu S (hAF hS)) (fun H hH hsun => hf H (hH.trans hAF) hsun)
    hiA (by omega) x
  have hBcap := Erdos20ExtremalStructure.intersecting_card_ge_seven_degree_le_five B
    (fun S hS => hu S (hBF hS)) (fun H hH hsun => hf H (hH.trans hBF) hsun)
    hiB (by omega) x
  by_cases hxA : x ∈ support A
  · apply (Finset.card_le_card (show F.filter (fun S => x ∈ S) ⊆
        A.filter (fun S => x ∈ S) from ?_)).trans hAcap
    intro S hS
    obtain ⟨hSF,hxS⟩ := Finset.mem_filter.mp hS
    have hSA : S ∈ A := by
      rw [hF] at hSF
      rcases Finset.mem_union.mp hSF with hSA | hSB
      · exact hSA
      · exact False.elim (Finset.disjoint_left.mp hsep hxA
          (Finset.mem_biUnion.mpr ⟨S,hSB,hxS⟩))
    exact Finset.mem_filter.mpr ⟨hSA,hxS⟩
  · apply (Finset.card_le_card (show F.filter (fun S => x ∈ S) ⊆
        B.filter (fun S => x ∈ S) from ?_)).trans hBcap
    intro S hS
    obtain ⟨hSF,hxS⟩ := Finset.mem_filter.mp hS
    have hSB : S ∈ B := by
      rw [hF] at hSF
      rcases Finset.mem_union.mp hSF with hSA | hSB
      · exact False.elim (hxA (Finset.mem_biUnion.mpr ⟨S,hSA,hxS⟩))
      · exact hSB
    exact Finset.mem_filter.mpr ⟨hSB,hxS⟩

/-- Every pair containing a degree-seventeen point has codegree at most five. -/
theorem degree_seventeen_pair_codegree_le_five
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (hm : ∀ R ∈ F, 54 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card)
    (x y : α) (hx : degree F x = 17) (hxy : x ≠ y) :
    (upperStar F {x,y}).card ≤ 5 := by
  classical
  have hcap := triple_seventeen_min_disjoint_eight_degree_le_five (residualLink F {x})
    (by simpa using residualLink_uniform (core := {x}) hu)
    (residualLink_sunflowerFree hf)
    (by simpa [card_residualLink,upperStar,degree] using hx)
    (degree_seventeen_link_min_disjoint_eight F hu hf hm x hx) y
  have he := card_filter_residualLink F ({x} : Finset α) {y} (by simpa using hxy.symm)
  simp only [Finset.singleton_subset_iff,Finset.singleton_union] at he
  rw [he] at hcap
  exact hcap

end Erdos20V11DegreeSeventeen
