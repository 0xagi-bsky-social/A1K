import SunflowerLean.Erdos20V8Stability

namespace FrontierMinimumTransversals
open Erdos20BCWConditional Erdos20ExtremalTwenty Erdos20ExtremalTransversals
open Erdos20V8Stability

/-- Version with a prescribed pair of components, preserving the synchronized
choice of the two designs throughout a later extension argument. -/
theorem two_designs_transversal_six
    {α : Type*} [DecidableEq α] (H K : Finset (Finset α))
    (hHu : ∀ P ∈ H, P.card = 3) (hKu : ∀ P ∈ K, P.card = 3)
    (hHf : IsSunflowerFree H 3) (hKf : IsSunflowerFree K 3)
    (hHi : ∀ P ∈ H, ∀ Q ∈ H, (P ∩ Q).Nonempty)
    (hKi : ∀ P ∈ K, ∀ Q ∈ K, (P ∩ Q).Nonempty)
    (hHc : H.card = 10) (hKc : K.card = 10)
    (hdis : Disjoint (support H) (support K))
    (C : Finset α) (hC : C.card = 6)
    (hHhit : ∀ P ∈ H, (P ∩ C).Nonempty)
    (hKhit : ∀ P ∈ K, (P ∩ C).Nonempty) :
    C ∩ support H ∈ H ∧ C ∩ support K ∈ K ∧
      C = (C ∩ support H) ∪ (C ∩ support K) := by
  classical
  let P := C ∩ support H
  let Q := C ∩ support K
  have hPhit : ∀ S ∈ H, (S ∩ P).Nonempty :=
    transversal_restrict_support H H C (Finset.Subset.refl _) hHhit
  have hQhit : ∀ S ∈ K, (S ∩ Q).Nonempty :=
    transversal_restrict_support K K C (Finset.Subset.refl _) hKhit
  have hPmin := intersecting_ten_transversal_card_ge_three H hHu hHf hHi hHc P hPhit
  have hQmin := intersecting_ten_transversal_card_ge_three K hKu hKf hKi hKc Q hQhit
  have hPQ : Disjoint P Q := hdis.mono Finset.inter_subset_right Finset.inter_subset_right
  have hPQsub : P ∪ Q ⊆ C := Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
  have hsum := Finset.card_le_card hPQsub
  rw [Finset.card_union_of_disjoint hPQ,hC] at hsum
  have hP3 : P.card = 3 := by omega
  have hQ3 : Q.card = 3 := by omega
  refine ⟨(ten_three_point_transversal_iff_member H hHu hHf hHi hHc P hP3).mp hPhit,
    (ten_three_point_transversal_iff_member K hKu hKf hKi hKc Q hQ3).mp hQhit,?_⟩
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le hPQsub
  rw [Finset.card_union_of_disjoint hPQ,hP3,hQ3,hC]

/-- Every minimum transversal of an extremal twenty-triple family is exactly
the union of two disjoint members. This classifies all minimum transversals,
not merely the existence of one. -/
theorem twenty_transversal_six_eq_two_disjoint_members
    {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hu : ∀ P ∈ L, P.card = 3) (hf : IsSunflowerFree L 3) (hc : L.card = 20)
    (C : Finset α) (hC : C.card = 6)
    (hhit : ∀ P ∈ L, (P ∩ C).Nonempty) :
    ∃ P ∈ L, ∃ Q ∈ L, Disjoint P Q ∧ C = P ∪ Q := by
  classical
  obtain ⟨H,K,hL,hdis,hdesign⟩ := extremal_twenty_two_disjoint_designs L hu hf hc
  have hHsub : H ⊆ L := by rw [hL]; exact Finset.subset_union_left
  have hKsub : K ⊆ L := by rw [hL]; exact Finset.subset_union_right
  have hH := hdesign H (by simp)
  have hK := hdesign K (by simp)
  have hHu : ∀ P ∈ H, P.card = 3 := fun P hP => hu P (hHsub hP)
  have hKu : ∀ P ∈ K, P.card = 3 := fun P hP => hu P (hKsub hP)
  have hHf : IsSunflowerFree H 3 := fun G hG hsun => hf G (hG.trans hHsub) hsun
  have hKf : IsSunflowerFree K 3 := fun G hG hsun => hf G (hG.trans hKsub) hsun
  let P := C ∩ support H
  let Q := C ∩ support K
  have hPhit : ∀ S ∈ H, (S ∩ P).Nonempty :=
    transversal_restrict_support L H C hHsub hhit
  have hQhit : ∀ S ∈ K, (S ∩ Q).Nonempty :=
    transversal_restrict_support L K C hKsub hhit
  have hPmin := intersecting_ten_transversal_card_ge_three H hHu hHf hH.2.1 hH.1 P hPhit
  have hQmin := intersecting_ten_transversal_card_ge_three K hKu hKf hK.2.1 hK.1 Q hQhit
  have hPQ : Disjoint P Q := hdis.mono Finset.inter_subset_right Finset.inter_subset_right
  have hPQsub : P ∪ Q ⊆ C := Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
  have hsum := Finset.card_le_card hPQsub
  rw [Finset.card_union_of_disjoint hPQ,hC] at hsum
  have hP3 : P.card = 3 := by omega
  have hQ3 : Q.card = 3 := by omega
  have hPm : P ∈ H := (ten_three_point_transversal_iff_member H hHu hHf hH.2.1 hH.1 P hP3).mp hPhit
  have hQm : Q ∈ K := (ten_three_point_transversal_iff_member K hKu hKf hK.2.1 hK.1 Q hQ3).mp hQhit
  refine ⟨P,hHsub hPm,Q,hKsub hQm,hPQ,?_⟩
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le hPQsub
  rw [Finset.card_union_of_disjoint hPQ,hP3,hQ3,hC]

end FrontierMinimumTransversals
