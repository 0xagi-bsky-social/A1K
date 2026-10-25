import SunflowerLean.Erdos20DesignSeparation
import SunflowerLean.Erdos20TracePatterns

/-! Local coordinates for the six-point extremal intersecting design. -/
namespace Erdos20DesignCoordinates
open Erdos20BCWConditional Erdos20MixedCross Erdos20RankThree Erdos20V5Frontier

/-- Two distinct extensions saturate a pair in a sunflower-free triple family. -/
theorem pair_star_eq_of_two {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (A B C : Finset α) (hA : A ∈ F) (hB : B ∈ F) (hne : A ≠ B)
    (hCA : C ⊆ A) (hCB : C ⊆ B) (hC : C.card = 2) :
    F.filter (fun S => C ⊆ S) = {A,B} := by
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · intro S hS
    simp only [Finset.mem_insert,Finset.mem_singleton] at hS
    rcases hS with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hA,hCA⟩
    · exact Finset.mem_filter.mpr ⟨hB,hCB⟩
  · simpa [hne] using triple_pair_degree_le_two F hu hf C hC

/-- Each anchor pair has one other extension, outside the anchor. -/
theorem ten_pair_trace_card_one {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 10)
    (R C : Finset α) (hR : R ∈ F) (hCR : C ⊆ R) (hC : C.card = 2) :
    (exactTrace F R C).card = 1 := by
  classical
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hC
  have haR : a ∈ R := hCR (by simp)
  have hbR : b ∈ R := hCR (by simp)
  obtain ⟨_,_,hp⟩ := intersecting_ten_design F hu hf hi hc
  have hpair := hp a (member_subset_support hR haR) b (member_subset_support hR hbR) hab
  have he : F.filter (fun S => ({a,b} : Finset α) ⊆ S) = insert R (exactTrace F R {a,b}) := by
    ext S
    simp only [Finset.mem_filter,Finset.mem_insert,exactTrace]
    constructor
    · rintro ⟨hSF,habS⟩
      by_cases hSR : S = R
      · exact Or.inl hSR
      · right
        refine ⟨hSF,?_⟩
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          by_contra hxp
          have hsub : insert x {a,b} ⊆ S ∩ R := by
            exact Finset.insert_subset_iff.mpr ⟨hx,Finset.subset_inter habS hCR⟩
          have hfull : S ∩ R = R := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by
            have hh := Finset.card_le_card hsub
            rw [Finset.card_insert_of_notMem hxp] at hh
            simp [hab,hu R hR] at hh ⊢
            omega)
          have hRS : R ⊆ S := by rw [← hfull]; exact Finset.inter_subset_left
          exact hSR (Finset.eq_of_subset_of_card_le hRS (by rw [hu S hSF,hu R hR])).symm
        · have hlo := Finset.card_le_card (Finset.subset_inter habS hCR)
          exact hlo
    · rintro (rfl | ⟨hSF,hint⟩)
      · exact ⟨hR,hCR⟩
      · exact ⟨hSF,by rw [← hint]; exact Finset.inter_subset_left⟩
  have hn : R ∉ exactTrace F R {a,b} := by
    intro hm
    have heR : R = {a,b} := by simpa using (Finset.mem_filter.mp hm).2
    have hh := hu R hR
    simp [heR,hab] at hh
  rw [he,Finset.card_insert_of_notMem hn] at hpair
  omega

end Erdos20DesignCoordinates
