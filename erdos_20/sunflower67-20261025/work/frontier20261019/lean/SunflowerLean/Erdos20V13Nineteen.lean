import SunflowerLean.Erdos20V12Nineteen


namespace Erdos20V13Nineteen
open Erdos20BCWConditional Erdos20Incidence Erdos20V12Nineteen
open Erdos20V8Intersecting Erdos20ExtremalTransversals Erdos20RankThreeEven

theorem nineteen_max_degree_five_transversal_ge_six
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card=3) (hf : IsSunflowerFree F 3) (hc : F.card=19)
    (hd : ∀ x, (F.filter (fun S => x ∈ S)).card≤5)
    (C : Finset α) (hhit : ∀ S ∈ F, (S ∩ C).Nonempty) : 6 ≤ C.card := by
  classical
  obtain ⟨H,K,hF,hHc,hKc,hdis,hHi,hKi⟩ := nineteen_max_degree_five_decomposition F hu hf hc hd
  have hHF : H ⊆ F := by rw [hF]; exact Finset.subset_union_left
  have hKF : K ⊆ F := by rw [hF]; exact Finset.subset_union_right
  have hHf : IsSunflowerFree H 3 := fun G hG hg => hf G (hG.trans hHF) hg
  have hKf : IsSunflowerFree K 3 := fun G hG hg => hf G (hG.trans hKF) hg
  have hH := intersecting_nine_transversal_card_ge_three H (C ∩ support H)
    (fun S hS => hu S (hHF hS)) hHf hHi (by omega)
    (transversal_restrict_support F H C hHF hhit)
  have hK := intersecting_nine_transversal_card_ge_three K (C ∩ support K)
    (fun S hS => hu S (hKF hS)) hKf hKi (by omega)
    (transversal_restrict_support F K C hKF hhit)
  have hCd : Disjoint (C ∩ support H) (C ∩ support K) :=
    hdis.mono Finset.inter_subset_right Finset.inter_subset_right
  have hsub : (C ∩ support H) ∪ (C ∩ support K) ⊆ C :=
    Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hCd] at hcard
  omega

theorem nineteen_transversal_five_has_degree_six
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card=3) (hf : IsSunflowerFree F 3) (hc : F.card=19)
    (C : Finset α) (hC : C.card≤5) (hhit : ∀ S ∈ F, (S ∩ C).Nonempty) :
    ∃ x, (F.filter (fun S => x ∈ S)).card=6 := by
  by_contra hn
  push_neg at hn
  have hd : ∀ x, (F.filter (fun S => x ∈ S)).card≤5 := by
    intro x
    have hb := rank_three_degree_le_six F hu hf x
    have he := hn x
    omega
  have h := nineteen_max_degree_five_transversal_ge_six F hu hf hc hd C hhit
  omega
/-- A support-restricted maximum degree is equivalent to the ambient formulation.
No finiteness assumption on the ambient type is used. -/
theorem max_degree_iff_on_support
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (d : ℕ) :
    (∀ x, (F.filter (fun S => x ∈ S)).card ≤ d) ↔
    (∀ x ∈ support F, (F.filter (fun S => x ∈ S)).card ≤ d) := by
  constructor
  · intro h x _
    exact h x
  · intro h x
    by_cases hx : x ∈ support F
    · exact h x hx
    · rw [Erdos20DesignConsequences.degree_eq_zero_of_not_support F x hx]
      exact Nat.zero_le d

/-- Choosing one triple from each disjoint intersecting component produces a
six-point transversal, establishing the upper half of the exact value. -/
theorem nineteen_max_degree_five_exists_transversal_six
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card=3) (hf : IsSunflowerFree F 3) (hc : F.card=19)
    (hd : ∀ x, (F.filter (fun S => x ∈ S)).card≤5) :
    ∃ C : Finset α, C ⊆ support F ∧ C.card=6 ∧
      ∀ S ∈ F, (S ∩ C).Nonempty := by
  classical
  obtain ⟨H,K,hF,hHc,hKc,hdis,hHi,hKi⟩ :=
    nineteen_max_degree_five_decomposition F hu hf hc hd
  have hHF : H ⊆ F := by rw [hF]; exact Finset.subset_union_left
  have hKF : K ⊆ F := by rw [hF]; exact Finset.subset_union_right
  obtain ⟨A,hA⟩ := Finset.card_pos.mp (show 0 < H.card by omega)
  obtain ⟨B,hB⟩ := Finset.card_pos.mp (show 0 < K.card by omega)
  have hAB : Disjoint A B := hdis.mono (member_subset_support hA) (member_subset_support hB)
  refine ⟨A ∪ B, Finset.union_subset (member_subset_support (hHF hA))
    (member_subset_support (hKF hB)), ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hAB, hu A (hHF hA), hu B (hKF hB)]
  · intro S hS
    rw [hF] at hS
    rcases Finset.mem_union.mp hS with hS | hS
    · obtain ⟨x,hx⟩ := hHi S hS A hA
      exact ⟨x,Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
        Finset.mem_union_left _ (Finset.mem_inter.mp hx).2⟩⟩
    · obtain ⟨x,hx⟩ := hKi S hS B hB
      exact ⟨x,Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
        Finset.mem_union_right _ (Finset.mem_inter.mp hx).2⟩⟩

/-- The transversal number is exactly six, expressed without an auxiliary
minimum convention: every transversal has at least six points, and one
supported transversal has exactly six. -/
theorem nineteen_max_degree_five_transversal_exact_six
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card=3) (hf : IsSunflowerFree F 3) (hc : F.card=19)
    (hd : ∀ x, (F.filter (fun S => x ∈ S)).card≤5) :
    (∀ C : Finset α, (∀ S ∈ F, (S ∩ C).Nonempty) → 6 ≤ C.card) ∧
    ∃ C : Finset α, C ⊆ support F ∧ C.card=6 ∧
      ∀ S ∈ F, (S ∩ C).Nonempty := by
  exact ⟨fun C hC => nineteen_max_degree_five_transversal_ge_six F hu hf hc hd C hC,
    nineteen_max_degree_five_exists_transversal_six F hu hf hc hd⟩

end Erdos20V13Nineteen

#print axioms Erdos20V13Nineteen.nineteen_max_degree_five_transversal_ge_six
#print axioms Erdos20V13Nineteen.nineteen_transversal_five_has_degree_six
#print axioms Erdos20V13Nineteen.max_degree_iff_on_support
#print axioms Erdos20V13Nineteen.nineteen_max_degree_five_exists_transversal_six
#print axioms Erdos20V13Nineteen.nineteen_max_degree_five_transversal_exact_six

