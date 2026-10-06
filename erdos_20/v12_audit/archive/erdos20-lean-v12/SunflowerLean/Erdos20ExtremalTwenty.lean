import SunflowerLean.Erdos20ExtremalSupport
import SunflowerLean.Erdos20GraphEqualityEndpoint
import SunflowerLean.Erdos20DesignSeparation

/-! Every extremal twenty-member triple family has a bipartite disjointness graph.
The equality case is excluded by incidence divisibility, without assuming a
classification of extremizers or a five-cycle blowup theorem. -/
namespace Erdos20ExtremalTwenty

open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence Erdos20RankThree
  Erdos20RankThreeEven Erdos20SharpTriples Erdos20ExtremalSupport

/-- The singleton trace classes on a triple have total capacity nine. -/
theorem singleton_intersection_card_le_nine
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) :
    (F.filter (fun S => (S ∩ R).card = 1)).card ≤ 9 := by
  classical
  have hs : F.filter (fun S => (S ∩ R).card = 1) ⊆
      R.biUnion (fun x => exactTrace F R {x}) := by
    intro S hS
    obtain ⟨hSF,hSR⟩ := Finset.mem_filter.mp hS
    obtain ⟨x,hx⟩ := Finset.card_eq_one.mp hSR
    have hxR : x ∈ R := by
      have hxSR : x ∈ S ∩ R := by rw [hx]; simp
      exact (Finset.mem_inter.mp hxSR).2
    exact Finset.mem_biUnion.mpr ⟨x,hxR,Finset.mem_filter.mpr ⟨hSF,hx⟩⟩
  calc
    _ ≤ (R.biUnion (fun x => exactTrace F R {x})).card := Finset.card_le_card hs
    _ ≤ ∑ x ∈ R, (exactTrace F R {x}).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ R, 3 := Finset.sum_le_sum
      (fun x _ => singleton_trace_card_le_three F R {x} hR hu hf (by simp))
    _ = 9 := by simp [hu R hR]

/-- A triple anchor contributes one excess incidence over the corrected
two-per-meeting-member baseline. -/
theorem triple_meeting_incidence_defect
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α)
    (hR : R ∈ F) (hR3 : R.card = 3) :
    2 * (F.filter (fun S => (S ∩ R).Nonempty)).card + 1 ≤
      (∑ x ∈ R, (F.filter (fun S => x ∈ S)).card) +
        (F.filter (fun S => (S ∩ R).card = 1)).card := by
  classical
  have hs : (∑ S ∈ F, (2 * (if (S ∩ R).Nonempty then 1 else 0) +
      if S = R then 1 else 0)) ≤
      ∑ S ∈ F, ((S ∩ R).card + if (S ∩ R).card = 1 then 1 else 0) := by
    apply Finset.sum_le_sum
    intro S _
    by_cases he : S = R
    · subst S
      have hn : R.Nonempty := Finset.card_pos.mp (by omega)
      simp [hR3, hn]
    · by_cases hn : (S ∩ R).Nonempty
      · have hp := hn.card_pos
        by_cases h1 : (S ∩ R).card = 1
        · simp [he, hn, h1]
        · simp [he, hn, h1]; omega
      · simp [he, hn]
  have hm : (∑ S ∈ F, if (S ∩ R).Nonempty then 1 else 0) =
      (F.filter (fun S => (S ∩ R).Nonempty)).card := by simp
  have hself : (∑ S ∈ F, if S = R then 1 else 0) = 1 := by simp [hR]
  have hsingle : (∑ S ∈ F, if (S ∩ R).card = 1 then 1 else 0) =
      (F.filter (fun S => (S ∩ R).card = 1)).card := by simp
  simp only [Finset.sum_add_distrib] at hs
  rw [← Finset.mul_sum, hm, hself, hsingle, incidence_sum_eq] at hs
  exact hs

/-- The excess over degree five on a member is its number of degree-six points. -/
theorem member_degree_sum_le_fifteen_add_saturated
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) :
    (∑ x ∈ R, (F.filter (fun S => x ∈ S)).card) ≤
      15 + (R ∩ degreeSixPoints F).card := by
  classical
  have hd : ∀ x ∈ R, (F.filter (fun S => x ∈ S)).card ≤
      5 + if x ∈ degreeSixPoints F then 1 else 0 := by
    intro x hx
    have hcap := rank_three_degree_le_six F hu hf x
    by_cases hb : x ∈ degreeSixPoints F
    · simp [hb]; omega
    · have hne : (F.filter (fun S => x ∈ S)).card ≠ 6 := by
        intro h6
        exact hb (Finset.mem_filter.mpr ⟨member_subset_support hR hx, h6⟩)
      simp [hb]; omega
  have hi : (∑ x ∈ R, if x ∈ degreeSixPoints F then 1 else 0) =
      (R ∩ degreeSixPoints F).card := by
    rw [← Finset.sum_filter]
    simp [Finset.filter_mem_eq_inter]
  calc
    _ ≤ ∑ x ∈ R, (5 + if x ∈ degreeSixPoints F then 1 else 0) := Finset.sum_le_sum hd
    _ = _ := by rw [Finset.sum_add_distrib, hi]; simp [hu R hR]

/-- For an extremal family the closed meeting neighborhood has at most twelve members. -/
theorem extremal_meeting_card_le_twelve
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (hc : F.card = 20)
    (R : Finset α) (hR : R ∈ F) :
    (F.filter (fun S => (S ∩ R).Nonempty)).card ≤ 12 := by
  have hdef := triple_meeting_incidence_defect F R hR (hu R hR)
  have hsingle := singleton_intersection_card_le_nine F R hR hu hf
  have hsum := member_degree_sum_le_fifteen_add_saturated F R hR hu hf
  have hsat := extremal_member_saturated_card_le_one F hu hf hc R hR
  omega

/-- The disjointness graph of an extremal family meets the equality AES threshold. -/
theorem extremal_disjointness_degree_ge_eight
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (hc : F.card = 20)
    (R : F) : 8 ≤ (disjointnessGraph F).degree R := by
  rw [disjointnessGraph_degree_eq F hu R]
  have hN := extremal_meeting_card_le_twelve F hu hf hc R.val R.property
  have hs := Finset.filter_card_add_filter_neg_card_eq_card
    (s := F) (p := fun S => (S ∩ R.val).Nonempty)
  simp only [Finset.not_nonempty_iff_eq_empty] at hs
  omega

/-- Equality at degree eight forces exactly one degree-six point in the corresponding triple. -/
theorem graph_degree_eight_member_saturated_eq_one
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (hc : F.card = 20)
    (R : F) (hd : (disjointnessGraph F).degree R = 8) :
    (R.val ∩ degreeSixPoints F).card = 1 := by
  rw [disjointnessGraph_degree_eq F hu R] at hd
  have hs := Finset.filter_card_add_filter_neg_card_eq_card
    (s := F) (p := fun S => (S ∩ R.val).Nonempty)
  simp only [Finset.not_nonempty_iff_eq_empty] at hs
  have hdef := triple_meeting_incidence_defect F R.val R.property (hu R.val R.property)
  have hsingle := singleton_intersection_card_le_nine F R.val R.property hu hf
  have hsum := member_degree_sum_le_fifteen_add_saturated F R.val R.property hu hf
  have hsat := extremal_member_saturated_card_le_one F hu hf hc R.val R.property
  omega

/-- The nonbipartite equality case is impossible: it would give six times
the number of saturated points equal to twenty. -/
theorem extremal_disjointnessGraph_two_colorable
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (hc : F.card = 20) :
    (disjointnessGraph F).Colorable 2 := by
  classical
  by_contra hnot
  have hreg := Erdos20GraphEqualityEndpoint.twenty_vertex_nonbipartite_regular
    (disjointnessGraph F) (by simpa using hc)
    (disjointnessGraph_triangle_free F hf)
    (extremal_disjointness_degree_ge_eight F hu hf hc) hnot
  have hpoint : ∀ R ∈ F, (R ∩ degreeSixPoints F).card = 1 := by
    intro R hR
    exact graph_degree_eight_member_saturated_eq_one F hu hf hc ⟨R,hR⟩ (hreg ⟨R,hR⟩)
  have hinc := incidence_sum_eq F (degreeSixPoints F)
  have hl : (∑ R ∈ F, (R ∩ degreeSixPoints F).card) = 20 := by
    calc
      _ = ∑ _R ∈ F, 1 := Finset.sum_congr rfl hpoint
      _ = _ := by simp [hc]
  have hr : (∑ x ∈ degreeSixPoints F, (F.filter (fun S => x ∈ S)).card) =
      (degreeSixPoints F).card * 6 := by
    calc
      _ = ∑ _x ∈ degreeSixPoints F, 6 :=
        Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2)
      _ = _ := by simp
  rw [hl, hr] at hinc
  omega

/-- Every extremal twenty-member triple family contains an intersecting
extremal ten-member subfamily, with no extra structural hypothesis. -/
theorem extremal_twenty_contains_intersecting_ten
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (hc : F.card = 20) :
    ∃ H ⊆ F, H.card = 10 ∧ ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty := by
  classical
  obtain ⟨c⟩ := extremal_disjointnessGraph_two_colorable F hu hf hc
  let classes : Fin 2 → Finset (Finset α) := fun i =>
    (Finset.univ.filter (fun S : F => c S = i)).image Subtype.val
  have hmem : ∀ i S, S ∈ classes i ↔ ∃ hS : S ∈ F, c ⟨S,hS⟩ = i := by
    intro i S
    simp only [classes, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨T, hi, rfl⟩
      exact ⟨T.property, hi⟩
    · rintro ⟨hS, hi⟩
      exact ⟨⟨S,hS⟩, hi, rfl⟩
  have hsub : ∀ i, classes i ⊆ F := by
    intro i S hS
    exact ((hmem i S).mp hS).choose
  have hinter : ∀ i, ∀ S ∈ classes i, ∀ T ∈ classes i, (S ∩ T).Nonempty := by
    intro i S hS T hT
    obtain ⟨hSF, hcS⟩ := (hmem i S).mp hS
    obtain ⟨hTF, hcT⟩ := (hmem i T).mp hT
    by_contra hnot
    have hi : S ∩ T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    have hne : (⟨S,hSF⟩ : F) ≠ ⟨T,hTF⟩ := by
      intro heq
      have hv : S = T := congrArg Subtype.val heq
      have he : S = ∅ := by simpa [← hv] using hi
      have hs3 := hu S hSF
      simp [he] at hs3
    exact c.valid (show (disjointnessGraph F).Adj ⟨S,hSF⟩ ⟨T,hTF⟩ from ⟨hne,hi⟩)
      (hcS.trans hcT.symm)
  have hcap : ∀ i, (classes i).card ≤ 10 := by
    intro i
    exact Erdos20RankThree.intersecting_rank_three_card_le_ten _
      (fun S hS => hu S (hsub i hS))
      (fun H hH hsun => hf H (hH.trans (hsub i)) hsun) (hinter i)
  have hcover : F ⊆ Finset.univ.biUnion classes := by
    intro S hS
    exact Finset.mem_biUnion.mpr ⟨c ⟨S,hS⟩, Finset.mem_univ _,
      (hmem _ S).mpr ⟨hS,rfl⟩⟩
  have hsum : 20 ≤ (classes 0).card + (classes 1).card := by
    calc
      20 = F.card := hc.symm
      _ ≤ (Finset.univ.biUnion classes).card := Finset.card_le_card hcover
      _ ≤ ∑ i, (classes i).card := Finset.card_biUnion_le
      _ = _ := by simp [Fin.sum_univ_two]
  have hc0 := hcap 0
  have hc1 := hcap 1
  exact ⟨classes 0,hsub 0,by omega,hinter 0⟩

/-- Every extremal family is the union of two intersecting ten-member
2-(6,3,2) designs on disjoint supports. This is a parameter classification;
it does not assert a unique isomorphism type of the six-point design. -/
theorem extremal_twenty_two_disjoint_designs
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (hc : F.card = 20) :
    ∃ H K : Finset (Finset α), F = H ∪ K ∧
      Disjoint (support H) (support K) ∧
      ∀ C ∈ ({H,K} : Finset (Finset (Finset α))),
        C.card = 10 ∧ (∀ S ∈ C, ∀ T ∈ C, (S ∩ T).Nonempty) ∧
        (support C).card = 6 ∧
        (∀ x ∈ support C, (C.filter (fun S => x ∈ S)).card = 5) ∧
        (∀ x ∈ support C, ∀ y ∈ support C, x ≠ y →
          (C.filter (fun S => ({x,y} : Finset α) ⊆ S)).card = 2) := by
  classical
  obtain ⟨H,hHF,hHc,hHi⟩ := extremal_twenty_contains_intersecting_ten F hu hf hc
  have hHf : IsSunflowerFree H 3 := fun G hG hg => hf G (hG.trans hHF) hg
  obtain ⟨hHs,hHd,hHp⟩ := Erdos20V5Frontier.intersecting_ten_design H
    (fun S hS => hu S (hHF hS)) hHf hHi hHc
  obtain ⟨hKc,hKi,hdis,hKs,hKd,hKp⟩ :=
    Erdos20DesignSeparation.extremal_twenty_complement_design F H hu hf hHF hHi hHc hc
  refine ⟨H,F \ H,?_,hdis,?_⟩
  · exact (Finset.union_sdiff_of_subset hHF).symm
  · intro C hC
    simp only [Finset.mem_insert,Finset.mem_singleton] at hC
    rcases hC with rfl | rfl
    · exact ⟨hHc,hHi,hHs,hHd,hHp⟩
    · exact ⟨hKc,hKi,hKs,hKd,hKp⟩

/-- Every extremal twenty-member triple family has exactly twelve supported
points, and every supported point belongs to exactly five members. -/
theorem extremal_twenty_regular_twelve
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (hc : F.card = 20) :
    (support F).card = 12 ∧
      ∀ x ∈ support F, (F.filter (fun S => x ∈ S)).card = 5 := by
  obtain ⟨H,hHF,hHc,hHi⟩ := extremal_twenty_contains_intersecting_ten F hu hf hc
  exact Erdos20DesignSeparation.extremal_twenty_regular_twelve_of_intersecting_ten
    F H hu hf hHF hHi hHc hc

end Erdos20ExtremalTwenty
