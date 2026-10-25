import ProfileACounts

namespace FrontierTwoSideConcentration
open FrontierProfileACounts

/-- If two row types require disjoint nine-element subfamilies of a common
at-most-twelve-element set, the row types cannot both occur. -/
theorem concentrate_from_disjoint_completion_types
    {α : Type} [DecidableEq α] (M : ResidualProfileA α)
    (hI : Erdos20V8Targets.IntersectingRankFourUpper 27)
    (A B : Finset α)
    (hside : ∀ R ∈ M.rows 2, R \ M.O ⊆ A ∨ R \ M.O ⊆ B)
    (hA : ∀ R ∈ M.rows 2, R \ M.O ⊆ A →
      ∀ S ∈ M.rows 0, Disjoint R S → (S ∩ A).card = 1)
    (hB : ∀ R ∈ M.rows 2, R \ M.O ⊆ B →
      ∀ S ∈ M.rows 0, Disjoint R S → (S ∩ A).card = 3) :
    (∀ R ∈ M.rows 2, R \ M.O ⊆ A) ∨
    (∀ R ∈ M.rows 2, R \ M.O ⊆ B) := by
  by_cases hall : ∀ R ∈ M.rows 2, R \ M.O ⊆ A
  · exact Or.inl hall
  · right
    push_neg at hall
    obtain ⟨R,hR,hRnA⟩ := hall
    have hRB : R \ M.O ⊆ B := (hside R hR).resolve_left hRnA
    intro T hT
    by_contra hTnB
    have hTA : T \ M.O ⊆ A := (hside T hT).resolve_right hTnB
    let DR := (M.rows 0).filter (fun S => S ∩ R = ∅)
    let DT := (M.rows 0).filter (fun S => S ∩ T = ∅)
    have hr : 9 ≤ DR.card := M.two_row_nine_disjoint_zero R hR
    have ht : 9 ≤ DT.card := M.two_row_nine_disjoint_zero T hT
    have hd : Disjoint DR DT := by
      apply Finset.disjoint_left.mpr
      intro S hSR hST
      obtain ⟨hS,hSR⟩ := Finset.mem_filter.mp hSR
      obtain ⟨_,hST⟩ := Finset.mem_filter.mp hST
      have h3 := hB R hR hRB S hS (Finset.disjoint_iff_inter_eq_empty.mpr hSR).symm
      have h1 := hA T hT hTA S hS (Finset.disjoint_iff_inter_eq_empty.mpr hST).symm
      omega
    have hsub : DR ∪ DT ⊆ M.rows 0 :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hb := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd] at hb
    have h0 := (M.final_count_window hI).2.1
    omega

end FrontierTwoSideConcentration
