import SunflowerLean.Erdos20MeetingFiftySix
import SunflowerLean.Erdos20FortyOne
import SunflowerLean.Erdos20V6Bounds

/-! Version-seven rank-four bounds and their higher-rank propagation.
These remain rank-dependent estimates, not a fixed-base all-rank bound. -/
universe u
namespace Erdos20V7Bounds
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence Erdos20RankFour
open Erdos20SharpTriples Erdos20MeetingFiftySix Erdos20FortyOne

/-- The meeting bound fifty-six forces sufficiently large disjointness
graphs to be bipartite; the intersecting bound then excludes cardinality ninety-four. -/
theorem rank_four_card_le_ninety_three
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3) : F.card ≤ 93 := by
  classical
  by_contra hnot
  have hlarge : 94 ≤ F.card := by omega
  have hne : F.Nonempty := Finset.card_pos.mp (by omega)
  letI : Nonempty F := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  have hmin : F.card - 56 ≤ (disjointnessGraph F).minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro R
    rw [rank_four_disjointnessGraph_degree_eq F hu R]
    have hN := meeting_neighborhood_card_le_fifty_six F R.val R.property hu hf
    have hs := Finset.filter_card_add_filter_neg_card_eq_card
      (s := F) (p := fun S => (S ∩ R.val).Nonempty)
    simp only [Finset.not_nonempty_iff_eq_empty] at hs
    omega
  have hcol : (disjointnessGraph F).Colorable 2 := by
    apply SimpleGraph.colorable_of_cliqueFree_lt_minDegree
      (disjointnessGraph_triangle_free F hf)
    have hcard : Fintype.card F = F.card := Fintype.card_coe _
    simp only [hcard]
    omega
  have h82 := rank_four_card_le_eighty_two_of_two_colorable F hu hf hcol
  omega

/-- The index counts additional rank above four. -/
def rankFourBound : ℕ → ℕ
  | 0 => 93
  | n + 1 => 2 * ((n + 5) * rankFourBound n - (n + 4))

theorem rankFourBound_pos (n : ℕ) : 0 < rankFourBound n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hm : n + 4 < (n + 5) * rankFourBound n := by nlinarith
    simp only [rankFourBound]
    omega

/-- The checked seed ninety-three propagates through the refined incidence recurrence. -/
theorem propagated_rank_four_bound
    {α : Type u} [DecidableEq α] (F : Finset (Finset α)) (n : ℕ)
    (hu : ∀ S ∈ F, S.card = n + 4) (hf : IsSunflowerFree F 3) :
    F.card ≤ rankFourBound n := by
  induction n generalizing F with
  | zero => exact rank_four_card_le_ninety_three F hu hf
  | succ n ih =>
    have hd : ∀ x, (F.filter (fun S => x ∈ S)).card ≤ rankFourBound n := by
      intro x
      have hb := ih (residualLink F {x})
        (by simpa using (residualLink_uniform (core := {x}) hu))
        (residualLink_sunflowerFree hf)
      simpa [card_residualLink,upperStar] using hb
    have hb := card_le_refined_step F (n + 1 + 4) 3 (rankFourBound n)
      (by omega) (rankFourBound_pos n) hu hf hd
    simpa [rankFourBound,Nat.add_assoc] using hb

/-- Kernel-reduced values at ranks four through eight. -/
theorem rankFourBound_values :
    List.map rankFourBound [0,1,2,3,4] = [93,922,11054,154744,2475890] := by
  decide

/-- The new seed gives a strict improvement over every value of the version-six recurrence. -/
theorem rankFourBound_lt_v6 (n : ℕ) :
    rankFourBound n < Erdos20V6Bounds.rankFourBound n := by
  induction n with
  | zero => decide
  | succ n ih =>
    change 2 * ((n + 5) * rankFourBound n - (n + 4)) <
      2 * ((n + 5) * Erdos20V6Bounds.rankFourBound n - (n + 4))
    have hpos := rankFourBound_pos n
    have hlo : n + 4 < (n + 5) * rankFourBound n := by nlinarith
    have hprod := Nat.mul_lt_mul_of_pos_left ih (show 0 < n + 5 by omega)
    omega

/-- An explicit rank-five consequence. -/
theorem rank_five_card_le_nine_hundred_twenty_two
    {α : Type u} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 5) (hf : IsSunflowerFree F 3) : F.card ≤ 922 := by
  exact propagated_rank_four_bound F 1 hu hf

/-- An explicit rank-six consequence. -/
theorem rank_six_card_le_eleven_thousand_fifty_four
    {α : Type u} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 6) (hf : IsSunflowerFree F 3) : F.card ≤ 11054 := by
  exact propagated_rank_four_bound F 2 hu hf

end Erdos20V7Bounds
