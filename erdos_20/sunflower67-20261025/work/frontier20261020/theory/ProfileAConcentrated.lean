import CompletionMass
import ProfileASplit
import ProfileAFibers
import TwoSideConcentration

namespace FrontierProfileAConcentrated
open Erdos20DegreeCongruences
open Erdos20BCWConditional Erdos20StrictCore Erdos20V8Targets
open FrontierProfileACounts FrontierProfileASplit FrontierGenericHeavyExtensions
open FrontierUniqueDesignTails FrontierCompletionMass

variable {α : Type} [DecidableEq α] {M : ResidualProfileA α}

/-- A residual zero-row usable as a left extension of a right-design tail. -/
def tails (D : DesignPair M) : Finset (Finset α) :=
  (M.rows 0).filter (fun S =>
    (S ∩ support D.left).card = 1 ∧ S ∩ support D.right ∈ D.right ∧
    (S \ support D.right).card = 1)

theorem tails_card_le_ten (D : DesignPair M) : (tails D).card ≤ 10 := by
  apply ten_design_tails_card_le_ten M.F (tails D) D.right M.free
  · intro S hS
    exact M.residual_subset (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  · exact D.center_not_mem_right_support
  · intro S hS
    exact M.center_omitted S (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  · exact D.right_star
  · intro S hS
    exact (Finset.mem_filter.mp hS).2.2.1
  · intro S hS
    exact (Finset.mem_filter.mp hS).2.2.2
  · exact D.right_card

theorem completion_mem_tails (D : DesignPair M) (R S : Finset α)
    (hR : R ∈ M.rows 2) (hS : S ∈ M.rows 0) (hRS : Disjoint R S)
    (hside : R \ M.O ⊆ support D.left) : S ∈ tails D := by
  obtain ⟨a,ha,haA,han,hdesign,htail,hshape⟩ :=
    D.same_side_completion_point R S hR hS hRS hside
  have hdiff : (S \ support D.right).card = 1 := by
    have hc := Finset.card_sdiff_add_card_inter S (support D.right)
    rw [M.uniform_H S (Finset.mem_filter.mp hS).1,
      D.same_side_completion_right_card R S hR hS hRS hside] at hc
    omega
  exact Finset.mem_filter.mpr ⟨hS,by rw [ha]; simp,htail,hdiff⟩

theorem completion_meets_extensions (D : DesignPair M) (R S : Finset α)
    (hR : R ∈ M.rows 2) (hS : S ∈ M.rows 0) (hRS : Disjoint R S)
    (hside : R \ M.O ⊆ support D.left) :
    (S ∩ extensions D.left (R \ M.O)).Nonempty := by
  obtain ⟨a,ha,haA,han,hdesign,htail,hshape⟩ :=
    D.same_side_completion_point R S hR hS hRS hside
  have haSA : a ∈ S ∩ support D.left := by rw [ha]; simp
  exact ⟨a,Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp haSA).1,
    Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp haSA).2,han,hdesign⟩⟩⟩

/-- The at-least-nine actual disjoint completions of each two-row are carried
by the two possible extensions of its design-side pair. -/
theorem key_heavy (D : DesignPair M)
    (hside : ∀ R ∈ M.rows 2, R \ M.O ⊆ support D.left)
    (P : Finset α) (hP : P ∈ (M.rows 2).image (FrontierProfileAFibers.key M)) :
    9 ≤ ∑ a ∈ extensions D.left P, degree (tails D) a := by
  obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hP
  let G := (M.rows 0).filter (fun S => S ∩ R = ∅)
  have hn : 9 ≤ G.card := M.two_row_nine_disjoint_zero R hR
  have hg (S : Finset α) (hS : S ∈ G) : S ∈ M.rows 0 ∧ Disjoint R S := by
    obtain ⟨hS,hSR⟩ := Finset.mem_filter.mp hS
    exact ⟨hS,(Finset.disjoint_iff_inter_eq_empty.mpr hSR).symm⟩
  apply hn.trans
  apply card_le_degree_sum_of_meeting G (tails D) (extensions D.left (R \ M.O))
  · intro S hS
    exact completion_mem_tails D R S hR (hg S hS).1 (hg S hS).2 (hside R hR)
  · intro S hS
    exact completion_meets_extensions D R S hR (hg S hS).1 (hg S hS).2 (hside R hR)

/-- A same-side concentration would require at least twenty-four two-rows,
while the heavy extension keys and four-point outside fibers allow at most twenty. -/
theorem concentrated_impossible (D : DesignPair M)
    (hI : IntersectingRankFourUpper 27)
    (hside : ∀ R ∈ M.rows 2, R \ M.O ⊆ support D.left) : False := by
  let K := (M.rows 2).image (FrontierProfileAFibers.key M)
  have hK : K.card ≤ 5 := by
    apply heavy_design_keys_card_le_five D.left K (degree (tails D))
      D.left_uniform D.left_free D.left_intersecting D.left_card
    · exact FrontierProfileAFibers.key_card_two M
    · intro P hP
      obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hP
      exact hside R hR
    · have he := degree_sum_eq_card_of_singleton_intersection (tails D) (support D.left)
        (fun S hS => (Finset.mem_filter.mp hS).2.1)
      rw [he]
      exact tails_card_le_ten D
    · exact key_heavy D hside
  have hupper := FrontierProfileAFibers.rows_card_le_four_mul_keys M
  have hlower := (M.final_count_window hI).2.2.1
  change (M.rows 2).card ≤ 4 * K.card at hupper
  omega

end FrontierProfileAConcentrated
