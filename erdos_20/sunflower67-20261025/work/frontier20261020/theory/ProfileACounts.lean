import ProfileAOutside

namespace FrontierProfileACounts
open Erdos20BCWConditional Erdos20StrictCore Erdos20DegreeCongruences
open Erdos20V8Targets Erdos20V8DesignCounts Erdos20Incidence
open FrontierProfileAOutside

/-- Explicit actual-family interface before a synchronized two-design
coordinate choice. No excluded-profile conclusion occurs among its fields. -/
structure ResidualProfileA (α : Type) [DecidableEq α] where
  F : Finset (Finset α)
  H : Finset (Finset α)
  x : α
  O : Finset α
  uniform : ∀ R ∈ F, R.card = 4
  free : IsSunflowerFree F 3
  residual_subset : H ⊆ F
  residual_card : H.card = 61
  center_omitted : ∀ R ∈ H, x ∉ R
  link_card : (residualLink F {x}).card = 20
  outsiders_disjoint : Disjoint O (support (residualLink F {x}))
  outsiders_card : O.card = 4
  outside_degrees : ∀ v ∈ O, degree H v = 19
  inside_degrees : ∀ v, v ∉ O → degree H v ≤ 14

namespace ResidualProfileA
variable {α : Type} [DecidableEq α] (M : ResidualProfileA α)

def rows (k : ℕ) : Finset (Finset α) := M.H.filter (fun R => (R ∩ M.O).card = k)

theorem uniform_H : ∀ R ∈ M.H, R.card = 4 :=
  fun R hR => M.uniform R (M.residual_subset hR)

theorem free_H : IsSunflowerFree M.H 3 :=
  fun G hG hsun => M.free G (hG.trans M.residual_subset) hsun

theorem degree_le_nineteen (v : α) : degree M.H v ≤ 19 := by
  by_cases hv : v ∈ M.O
  · rw [M.outside_degrees v hv]
  · exact (M.inside_degrees v hv).trans (by decide)

theorem outsider_cap : ∀ R ∈ M.H, (R ∩ M.O).card ≤ 2 :=
  residual_sixty_one_outside_card_le_two M.F M.H M.uniform M.free M.residual_subset
    M.residual_card M.degree_le_nineteen M.x M.center_omitted M.link_card M.O M.outsiders_disjoint

theorem disjoint_outside_sum (R S : Finset α) (hR : R ∈ M.H) (hS : S ∈ M.H)
    (hRS : Disjoint R S) : (R ∩ M.O).card + (S ∩ M.O).card ≤ 2 :=
  disjoint_rows_outside_sum_le_two M.F M.uniform M.free M.x M.link_card M.O M.outsiders_disjoint
    R S (M.residual_subset hR) (M.residual_subset hS)
    (M.center_omitted R hR) (M.center_omitted S hS) hRS

theorem rows_two_intersecting :
    ∀ R ∈ M.rows 2, ∀ S ∈ M.rows 2, (R ∩ S).Nonempty := by
  intro R hR S hS
  obtain ⟨hRH,hR2⟩ := Finset.mem_filter.mp hR
  obtain ⟨hSH,hS2⟩ := Finset.mem_filter.mp hS
  by_contra hn
  have hRS := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp hn)
  have hb := M.disjoint_outside_sum R S hRH hSH hRS
  omega

theorem rows_two_card_le_twenty_seven (hI : IntersectingRankFourUpper 27) :
    (M.rows 2).card ≤ 27 := by
  apply hI
  · intro R hR
    exact M.uniform_H R (Finset.mem_filter.mp hR).1
  · exact fun G hG hsun => M.free_H G (hG.trans (Finset.filter_subset _ _)) hsun
  · exact M.rows_two_intersecting

theorem count_equations :
    (M.rows 0).card + (M.rows 1).card + (M.rows 2).card = 61 ∧
    (M.rows 1).card + 2 * (M.rows 2).card = 76 ∧
    (M.rows 2).card = (M.rows 0).card + 15 := by
  have ht := block_counts_total M.H M.O M.outsider_cap
  have hi := block_counts_first_moment M.H M.O M.outsider_cap
  rw [incidence_sum_eq] at hi
  have hs : (∑ v ∈ M.O, (M.H.filter (fun R => v ∈ R)).card) = 76 := by
    calc
      _ = ∑ _v ∈ M.O, 19 := Finset.sum_congr rfl (fun v hv => M.outside_degrees v hv)
      _ = 76 := by simp [M.outsiders_card]
  rw [hs] at hi
  change (M.rows 0).card + (M.rows 1).card + (M.rows 2).card = M.H.card at ht
  change 76 = (M.rows 1).card + 2 * (M.rows 2).card at hi
  rw [M.residual_card] at ht
  omega

theorem two_row_degree_sum (R : Finset α) (hR : R ∈ M.rows 2) :
    (∑ v ∈ R, degree M.H v) ≤ 66 := by
  obtain ⟨hRH,hR2⟩ := Finset.mem_filter.mp hR
  have hpart : Disjoint (R ∩ M.O) (R \ M.O) := by
    apply Finset.disjoint_left.mpr
    intro v hvI hvD
    exact (Finset.mem_sdiff.mp hvD).2 (Finset.mem_inter.mp hvI).2
  have hcover : (R ∩ M.O) ∪ (R \ M.O) = R := by
    ext v
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto
  have hdiff : (R \ M.O).card = 2 := by
    have hh := Finset.card_sdiff_add_card_inter R M.O
    rw [M.uniform_H R hRH,hR2] at hh
    omega
  calc
    _ = (∑ v ∈ R ∩ M.O, degree M.H v) + ∑ v ∈ R \ M.O, degree M.H v := by
      rw [← Finset.sum_union hpart,hcover]
    _ ≤ (∑ _v ∈ R ∩ M.O, 19) + ∑ _v ∈ R \ M.O, 14 := by
      apply Nat.add_le_add
      · exact Finset.sum_le_sum (fun v hv => (M.outside_degrees v (Finset.mem_inter.mp hv).2).le)
      · exact Finset.sum_le_sum (fun v hv => M.inside_degrees v (Finset.mem_sdiff.mp hv).2)
    _ = 66 := by simp [hR2,hdiff]

theorem two_row_nine_disjoint_zero (R : Finset α) (hR : R ∈ M.rows 2) :
    9 ≤ ((M.rows 0).filter (fun S => S ∩ R = ∅)).card := by
  have hn := FrontierMeetingDefect.sixty_one_degree_sum_sixty_six_has_nine_disjoint
    M.H R (Finset.mem_filter.mp hR).1 M.uniform_H M.free_H M.residual_card (M.two_row_degree_sum R hR)
  have he : M.H.filter (fun S => S ∩ R = ∅) =
      (M.rows 0).filter (fun S => S ∩ R = ∅) := by
    ext S
    simp only [rows,Finset.mem_filter]
    constructor
    · rintro ⟨hSH,hSR⟩
      have hb := M.disjoint_outside_sum R S (Finset.mem_filter.mp hR).1 hSH
        (Finset.disjoint_iff_inter_eq_empty.mpr hSR).symm
      have hR2 := (Finset.mem_filter.mp hR).2
      exact ⟨⟨hSH,by omega⟩,hSR⟩
    · rintro ⟨⟨hSH,_⟩,hSR⟩
      exact ⟨hSH,hSR⟩
  simpa only [he] using hn

theorem final_count_window (hI : IntersectingRankFourUpper 27) :
    9 ≤ (M.rows 0).card ∧ (M.rows 0).card ≤ 12 ∧
    24 ≤ (M.rows 2).card ∧ (M.rows 2).card ≤ 27 := by
  have he := M.count_equations
  have h2max := M.rows_two_card_le_twenty_seven hI
  have hpos : 0 < (M.rows 2).card := by omega
  obtain ⟨R,hR⟩ := Finset.card_pos.mp hpos
  have hn := (M.two_row_nine_disjoint_zero R hR).trans (Finset.card_filter_le _ _)
  omega

end ResidualProfileA
end FrontierProfileACounts
