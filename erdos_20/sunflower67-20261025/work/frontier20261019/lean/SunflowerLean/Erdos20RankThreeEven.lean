import SunflowerLean.Erdos20RankThree

/-! A degree-sensitive trace estimate excludes the odd endpoint twenty-three. -/
namespace Erdos20RankThreeEven
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence Erdos20RankThree

/-- The family disjoint from any anchor triple has at most ten members. -/
theorem disjoint_anchor_card_le_ten {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (R : Finset α) (hR : R ∈ F)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) :
    (F.filter (fun S => S ∩ R = ∅)).card ≤ 10 := by
  apply intersecting_rank_three_card_le_ten _
    (fun S hS => hu S (Finset.mem_filter.mp hS).1)
    (fun H hH hsun => hf H (hH.trans (Finset.filter_subset _ _)) hsun)
  intro S hS T hT
  exact disjoint_anchor_family_intersecting F R hR
    (Finset.card_pos.mp (by rw [hu R hR]; decide)) hf S hS T hT
    (Finset.card_pos.mp (by rw [hu S (Finset.mem_filter.mp hS).1]; decide))
    (Finset.card_pos.mp (by rw [hu T (Finset.mem_filter.mp hT).1]; decide))

/-- An anchor point gives a refined global bound: its own star, the at most
ten disjoint members, two singleton traces, and the opposite pair trace. -/
theorem rank_three_card_le_degree_add_seventeen
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (R : Finset α) (x : α) (hR : R ∈ F) (hx : x ∈ R)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) :
    F.card ≤ (F.filter (fun S => x ∈ S)).card + 17 := by
  classical
  let A := F.filter (fun S => x ∈ S)
  let D := F.filter (fun S => S ∩ R = ∅)
  let P := exactTrace F R (R.erase x)
  let Q := (R.erase x).biUnion (fun y => exactTrace F R {y})
  have hcover : F ⊆ (A ∪ D) ∪ (P ∪ Q) := by
    intro S hS
    by_cases hxS : x ∈ S
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hS,hxS⟩))
    · by_cases he : S ∩ R = ∅
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hS,he⟩))
      · have hproper : S ∩ R ≠ R := by
          intro heq
          have : x ∈ S ∩ R := by rw [heq]; exact hx
          exact hxS (Finset.mem_inter.mp this).1
        obtain ⟨y, hyR, hcase⟩ := nonempty_proper_subset_triple R (S ∩ R)
          (hu R hR) Finset.inter_subset_right (Finset.nonempty_iff_ne_empty.mpr he) hproper
        apply Finset.mem_union_right
        rcases hcase with hsingle | hpair
        · apply Finset.mem_union_right
          apply Finset.mem_biUnion.mpr
          have hyx : y ≠ x := by
            intro heq
            have : x ∈ S ∩ R := by rw [hsingle, heq]; simp
            exact hxS (Finset.mem_inter.mp this).1
          exact ⟨y, Finset.mem_erase.mpr ⟨hyx, hyR⟩, Finset.mem_filter.mpr ⟨hS, hsingle⟩⟩
        · apply Finset.mem_union_left
          have hyx : y = x := by
            by_contra hne
            have : x ∈ S ∩ R := by rw [hpair]; exact Finset.mem_erase.mpr ⟨Ne.symm hne,hx⟩
            exact hxS (Finset.mem_inter.mp this).1
          exact Finset.mem_filter.mpr ⟨hS, by simpa [hyx] using hpair⟩
  have hD : D.card ≤ 10 := disjoint_anchor_card_le_ten F R hR hu hf
  have hP : P.card ≤ 1 := pair_trace_card_le_one F R (R.erase x) hR hu hf
    (Finset.erase_subset _ _) (by rw [Finset.card_erase_of_mem hx, hu R hR])
  have hQ : Q.card ≤ 6 := by
    calc
      _ ≤ ∑ y ∈ R.erase x, (exactTrace F R {y}).card := Finset.card_biUnion_le
      _ ≤ ∑ _y ∈ R.erase x, 3 := Finset.sum_le_sum
        (fun y _ => singleton_trace_card_le_three F R {y} hR hu hf (by simp))
      _ = 6 := by simp [Finset.card_erase_of_mem hx, hu R hR]
  have h1 := Finset.card_le_card hcover
  have h2 := Finset.card_union_le (A ∪ D) (P ∪ Q)
  have h3 := Finset.card_union_le A D
  have h4 := Finset.card_union_le P Q
  change F.card ≤ A.card + 17
  omega

/-- Every point degree is at most six, by the verified rank-two link bound. -/
theorem rank_three_degree_le_six {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S ∈ F, S.card = 3)
    (hf : IsSunflowerFree F 3) (x : α) :
    (F.filter (fun S => x ∈ S)).card ≤ 6 := by
  have hb := rank_two_three_petals_card_le_six (residualLink F {x})
    (by simpa using (residualLink_uniform (core := {x}) hu))
    (residualLink_sunflowerFree hf)
  simpa [card_residualLink, upperStar] using hb

/-- A hypothetical twenty-three-member family would have degree six at every
point in its support. -/
theorem rank_three_card_twenty_three_degree_six
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hc : F.card = 23) (x : α) (hx : x ∈ support F) :
    (F.filter (fun S => x ∈ S)).card = 6 := by
  obtain ⟨R, hR, hxR⟩ := Finset.mem_biUnion.mp hx
  have hlo := rank_three_card_le_degree_add_seventeen F R x hR hxR hu hf
  have hhi := rank_three_degree_le_six F hu hf x
  omega

/-- The endpoint twenty-three is impossible: its incidence total would be
sixty-nine, while every supported point contributes six. -/
theorem rank_three_three_petals_card_le_twenty_two
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) : F.card ≤ 22 := by
  have hb := rank_three_three_petals_card_le_twenty_three F hu hf
  by_contra hnot
  have hc : F.card = 23 := by omega
  have hsum : (∑ S ∈ F, (S ∩ support F).card) = 69 := by
    calc
      _ = ∑ _S ∈ F, 3 := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [Finset.inter_eq_left.mpr (member_subset_support hS), hu S hS]
      _ = 69 := by simp [hc]
  have hinc := incidence_sum_eq F (support F)
  have hdegrees : (∑ x ∈ support F, (F.filter (fun S => x ∈ S)).card) =
      (support F).card * 6 := by
    calc
      _ = ∑ _x ∈ support F, 6 := Finset.sum_congr rfl
        (fun x hx => rank_three_card_twenty_three_degree_six F hu hf hc x hx)
      _ = _ := by simp
  rw [hsum, hdegrees] at hinc
  omega

end Erdos20RankThreeEven
