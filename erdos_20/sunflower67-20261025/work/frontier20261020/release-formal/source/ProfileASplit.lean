import ProfileACounts
import MinimumTransversals
import CompletionCompatibility

namespace FrontierProfileASplit
open Erdos20BCWConditional Erdos20StrictCore Erdos20RankThree
open Erdos20ExtremalTransversals
open FrontierProfileACounts FrontierProfileAOutside FrontierMinimumTransversals
open FrontierCompletionCompatibility

variable {α : Type} [DecidableEq α]

/-- Deleting the two outsider points from the union with a disjoint zero-row
leaves a genuine minimum transversal of the high link. -/
theorem disjoint_two_row_minimum_transversal
    (M : ResidualProfileA α) (R S : Finset α)
    (hR : R ∈ M.rows 2) (hS : S ∈ M.rows 0) (hRS : Disjoint R S) :
    ((R \ M.O) ∪ S).card = 6 ∧
      (∀ T ∈ residualLink M.F {M.x}, (T ∩ ((R \ M.O) ∪ S)).Nonempty) := by
  obtain ⟨hRH,hR2⟩ := Finset.mem_filter.mp hR
  obtain ⟨hSH,hS0⟩ := Finset.mem_filter.mp hS
  have hP2 : (R \ M.O).card = 2 := by
    have hp := Finset.card_sdiff_add_card_inter R M.O
    rw [M.uniform_H R hRH,hR2] at hp
    omega
  constructor
  · rw [Finset.card_union_of_disjoint (hRS.mono_left Finset.sdiff_subset),
      hP2,M.uniform_H S hSH]
  · intro T hT
    obtain ⟨v,hv⟩ := disjoint_rows_union_hits_link M.F M.uniform M.free M.x R S
      (M.residual_subset hRH) (M.residual_subset hSH)
      (M.center_omitted R hRH) (M.center_omitted S hSH) hRS T hT
    obtain ⟨hvT,hvRS⟩ := Finset.mem_inter.mp hv
    refine ⟨v,Finset.mem_inter.mpr ⟨hvT,?_⟩⟩
    rcases Finset.mem_union.mp hvRS with hvR | hvS
    · apply Finset.mem_union_left
      refine Finset.mem_sdiff.mpr ⟨hvR,?_⟩
      intro hvO
      exact Finset.disjoint_left.mp M.outsiders_disjoint hvO (member_subset_support hT hvT)
    · exact Finset.mem_union_right _ hvS

/-- A synchronized decomposition of the actual high link. -/
structure DesignPair (M : ResidualProfileA α) where
  left : Finset (Finset α)
  right : Finset (Finset α)
  link_eq : residualLink M.F {M.x} = left ∪ right
  disjoint_support : Disjoint (support left) (support right)
  left_uniform : ∀ T ∈ left, T.card = 3
  right_uniform : ∀ T ∈ right, T.card = 3
  left_free : IsSunflowerFree left 3
  right_free : IsSunflowerFree right 3
  left_intersecting : ∀ P ∈ left, ∀ Q ∈ left, (P ∩ Q).Nonempty
  right_intersecting : ∀ P ∈ right, ∀ Q ∈ right, (P ∩ Q).Nonempty
  left_card : left.card = 10
  right_card : right.card = 10

theorem exists_designPair (M : ResidualProfileA α) : Nonempty (DesignPair M) := by
  have hu : ∀ T ∈ residualLink M.F {M.x}, T.card = 3 := by
    simpa using residualLink_uniform (core := ({M.x} : Finset α)) M.uniform
  have hf := residualLink_sunflowerFree (core := ({M.x} : Finset α)) M.free
  obtain ⟨H,K,hL,hd,hD⟩ := Erdos20ExtremalTwenty.extremal_twenty_two_disjoint_designs
    _ hu hf M.link_card
  have hHs : H ⊆ residualLink M.F {M.x} := by rw [hL]; exact Finset.subset_union_left
  have hKs : K ⊆ residualLink M.F {M.x} := by rw [hL]; exact Finset.subset_union_right
  have hH := hD H (by simp)
  have hK := hD K (by simp)
  exact ⟨⟨H,K,hL,hd,(fun T hT => hu T (hHs hT)),(fun T hT => hu T (hKs hT)),
    (fun G hG hsun => hf G (hG.trans hHs) hsun),
    (fun G hG hsun => hf G (hG.trans hKs) hsun),hH.2.1,hK.2.1,hH.1,hK.1⟩⟩

namespace DesignPair
variable {M : ResidualProfileA α} (D : DesignPair M)

def swap : DesignPair M :=
  ⟨D.right,D.left,D.link_eq.trans (Finset.union_comm _ _),D.disjoint_support.symm,
    D.right_uniform,D.left_uniform,D.right_free,D.left_free,
    D.right_intersecting,D.left_intersecting,D.right_card,D.left_card⟩

theorem left_star (T : Finset α) (hT : T ∈ D.left) : insert M.x T ∈ M.F := by
  have hm : T ∈ residualLink M.F {M.x} := by rw [D.link_eq]; exact Finset.mem_union_left _ hT
  simpa using core_union_residual_mem_family hm

theorem right_star (T : Finset α) (hT : T ∈ D.right) : insert M.x T ∈ M.F :=
  D.swap.left_star T hT

theorem minimum_projections (R S : Finset α)
    (hR : R ∈ M.rows 2) (hS : S ∈ M.rows 0) (hRS : Disjoint R S) :
    ((R \ M.O) ∪ S) ∩ support D.left ∈ D.left ∧
    ((R \ M.O) ∪ S) ∩ support D.right ∈ D.right ∧
    (R \ M.O) ∪ S =
      (((R \ M.O) ∪ S) ∩ support D.left) ∪
      (((R \ M.O) ∪ S) ∩ support D.right) := by
  obtain ⟨hc,hh⟩ := disjoint_two_row_minimum_transversal M R S hR hS hRS
  apply two_designs_transversal_six D.left D.right D.left_uniform D.right_uniform
    D.left_free D.right_free D.left_intersecting D.right_intersecting
    D.left_card D.right_card D.disjoint_support _ hc
  · intro T hT
    apply hh T
    rw [D.link_eq]
    exact Finset.mem_union_left _ hT
  · intro T hT
    apply hh T
    rw [D.link_eq]
    exact Finset.mem_union_right _ hT

/-- Every two-row neighbor pair is inside the two design supports. -/
theorem pair_subset_support (R : Finset α) (hR : R ∈ M.rows 2) :
    R \ M.O ⊆ support D.left ∪ support D.right := by
  have hn := M.two_row_nine_disjoint_zero R hR
  obtain ⟨S,hS⟩ := Finset.card_pos.mp (show 0 < ((M.rows 0).filter (fun S => S ∩ R = ∅)).card by omega)
  obtain ⟨hS,hSR⟩ := Finset.mem_filter.mp hS
  have hm := D.minimum_projections R S hR hS (Finset.disjoint_iff_inter_eq_empty.mpr hSR).symm
  intro v hv
  have hvC : v ∈ (R \ M.O) ∪ S := Finset.mem_union_left _ hv
  rw [hm.2.2] at hvC
  rcases Finset.mem_union.mp hvC with h | h
  · exact Finset.mem_union_left _ (Finset.mem_inter.mp h).2
  · exact Finset.mem_union_right _ (Finset.mem_inter.mp h).2

theorem completion_subset_support (R S : Finset α)
    (hR : R ∈ M.rows 2) (hS : S ∈ M.rows 0) (hRS : Disjoint R S) :
    S ⊆ support D.left ∪ support D.right := by
  have hm := D.minimum_projections R S hR hS hRS
  intro v hv
  have hvC : v ∈ (R \ M.O) ∪ S := Finset.mem_union_right _ hv
  rw [hm.2.2] at hvC
  rcases Finset.mem_union.mp hvC with h | h
  · exact Finset.mem_union_left _ (Finset.mem_inter.mp h).2
  · exact Finset.mem_union_right _ (Finset.mem_inter.mp h).2

theorem completion_union (R S : Finset α)
    (hR : R ∈ M.rows 2) (hS : S ∈ M.rows 0) (hRS : Disjoint R S) :
    S = (S ∩ support D.left) ∪ (S ∩ support D.right) := by
  have hs := D.completion_subset_support R S hR hS hRS
  ext v
  simp only [Finset.mem_union,Finset.mem_inter]
  constructor
  · intro hv
    rcases Finset.mem_union.mp (hs hv) with h | h
    · exact Or.inl ⟨hv,h⟩
    · exact Or.inr ⟨hv,h⟩
  · tauto

/-- A split two-row pair forces every disjoint zero-row to be a pair of
point-link edges in the synchronized ten-designs. -/
theorem split_completion_links (R S : Finset α)
    (hR : R ∈ M.rows 2) (hS : S ∈ M.rows 0) (hRS : Disjoint R S)
    (a b : α) (ha : a ∈ support D.left) (hb : b ∈ support D.right)
    (hpair : R \ M.O = {a,b}) :
    S ∩ support D.left ∈ residualLink D.left {a} ∧
    S ∩ support D.right ∈ residualLink D.right {b} := by
  have hm := D.minimum_projections R S hR hS hRS
  have haR : a ∈ R := Finset.sdiff_subset (by rw [hpair]; simp)
  have hbR : b ∈ R := Finset.sdiff_subset (by rw [hpair]; simp)
  have haS : a ∉ S := fun h => Finset.disjoint_left.mp hRS haR h
  have hbS : b ∉ S := fun h => Finset.disjoint_left.mp hRS hbR h
  have haK : a ∉ support D.right := fun h => Finset.disjoint_left.mp D.disjoint_support ha h
  have hbH : b ∉ support D.left := fun h => Finset.disjoint_left.mp D.disjoint_support h hb
  have heH : ((R \ M.O) ∪ S) ∩ support D.left = insert a (S ∩ support D.left) := by
    ext v
    simp only [hpair,Finset.mem_inter,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    aesop
  have heK : ((R \ M.O) ∪ S) ∩ support D.right = insert b (S ∩ support D.right) := by
    ext v
    simp only [hpair,Finset.mem_inter,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    aesop
  constructor
  · apply mem_residualLink_iff.mpr
    refine ⟨insert a (S ∩ support D.left),heH ▸ hm.1,by simp,?_⟩
    ext v
    simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton,Finset.mem_inter]
    aesop
  · apply mem_residualLink_iff.mpr
    refine ⟨insert b (S ∩ support D.right),heK ▸ hm.2.1,by simp,?_⟩
    ext v
    simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton,Finset.mem_inter]
    aesop

/-- The actual-family split configuration is impossible: nine disjoint
zero-rows are required, whereas the two link coordinates permit at most four. -/
theorem no_split_pair (R : Finset α) (hR : R ∈ M.rows 2)
    (a b : α) (ha : a ∈ support D.left) (hb : b ∈ support D.right)
    (hpair : R \ M.O = {a,b}) : False := by
  let G := (M.rows 0).filter (fun S => S ∩ R = ∅)
  have hg (S : Finset α) (hS : S ∈ G) : S ∈ M.rows 0 ∧ Disjoint R S := by
    obtain ⟨hS,hd⟩ := Finset.mem_filter.mp hS
    exact ⟨hS,(Finset.disjoint_iff_inter_eq_empty.mpr hd).symm⟩
  have hGF : G ⊆ M.F := fun S hS => M.residual_subset (Finset.mem_filter.mp (hg S hS).1).1
  have hGne : ∀ S ∈ G, S.Nonempty := by
    intro S hS
    apply Finset.card_pos.mp
    rw [M.uniform S (hGF hS)]
    decide
  have hb4 : G.card ≤ 4 := by
    apply split_completions_card_le_four M.F D.left D.right G M.free
      D.left_uniform D.right_uniform D.left_free D.right_free
      D.left_intersecting D.right_intersecting D.left_card D.right_card D.disjoint_support
      M.x a b D.left_star D.right_star
      (fun S => S ∩ support D.left) (fun S => S ∩ support D.right) hGF
    · intro S hS
      exact (D.split_completion_links R S hR (hg S hS).1 (hg S hS).2 a b ha hb hpair).1
    · intro S hS
      exact (D.split_completion_links R S hR (hg S hS).1 (hg S hS).2 a b ha hb hpair).2
    · intro S hS
      exact D.completion_union R S hR (hg S hS).1 (hg S hS).2
    · intro S hS
      exact M.center_omitted S (Finset.mem_filter.mp (hg S hS).1).1
    · intro S hS T hT
      apply disjoint_anchor_family_intersecting M.F R
        (M.residual_subset (Finset.mem_filter.mp hR).1)
        (Finset.card_pos.mp (by rw [M.uniform_H R (Finset.mem_filter.mp hR).1]; decide)) M.free
        S (Finset.mem_filter.mpr ⟨hGF hS,Finset.disjoint_iff_inter_eq_empty.mp (hg S hS).2.symm⟩)
        T (Finset.mem_filter.mpr ⟨hGF hT,Finset.disjoint_iff_inter_eq_empty.mp (hg T hT).2.symm⟩)
        (hGne S hS) (hGne T hT)
  have hn : 9 ≤ G.card := M.two_row_nine_disjoint_zero R hR
  omega

/-- Every actual two-row has both non-outsider points on a single side. -/
theorem pair_one_side (R : Finset α) (hR : R ∈ M.rows 2) :
    R \ M.O ⊆ support D.left ∨ R \ M.O ⊆ support D.right := by
  have hcard : (R \ M.O).card = 2 := by
    have hc := Finset.card_sdiff_add_card_inter R M.O
    rw [M.uniform_H R (Finset.mem_filter.mp hR).1,(Finset.mem_filter.mp hR).2] at hc
    omega
  obtain ⟨a,b,hab,hpair⟩ := Finset.card_eq_two.mp hcard
  have hs := D.pair_subset_support R hR
  have ha := Finset.mem_union.mp (hs (by rw [hpair]; simp : a ∈ R \ M.O))
  have hb := Finset.mem_union.mp (hs (by rw [hpair]; simp : b ∈ R \ M.O))
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · left
    intro v hv
    rw [hpair] at hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ha
    · have he := Finset.mem_singleton.mp hv
      exact he ▸ hb
  · exact False.elim (D.no_split_pair R hR a b ha hb hpair)
  · exact False.elim (D.no_split_pair R hR b a hb ha (hpair.trans (Finset.pair_comm _ _)))
  · right
    intro v hv
    rw [hpair] at hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ha
    · have he := Finset.mem_singleton.mp hv
      exact he ▸ hb

/-- When both neighbor points lie in the left design, every disjoint
completion consists of one left point and a full right-design triple. -/
theorem same_side_completion (R S : Finset α)
    (hR : R ∈ M.rows 2) (hS : S ∈ M.rows 0) (hRS : Disjoint R S)
    (hside : R \ M.O ⊆ support D.left) :
    (S ∩ support D.left).card = 1 ∧
      S ∩ support D.right ∈ D.right ∧
      (R \ M.O) ∪ (S ∩ support D.left) ∈ D.left := by
  have hm := D.minimum_projections R S hR hS hRS
  have heH : ((R \ M.O) ∪ S) ∩ support D.left =
      (R \ M.O) ∪ (S ∩ support D.left) := by
    ext v
    simp only [Finset.mem_inter,Finset.mem_union]
    have hv := @hside v
    tauto
  have heK : ((R \ M.O) ∪ S) ∩ support D.right = S ∩ support D.right := by
    ext v
    simp only [Finset.mem_inter,Finset.mem_union]
    have hd : v ∈ R \ M.O → v ∉ support D.right :=
      fun hv hvK => Finset.disjoint_left.mp D.disjoint_support (hside hv) hvK
    tauto
  have hP2 : (R \ M.O).card = 2 := by
    have hp := Finset.card_sdiff_add_card_inter R M.O
    rw [M.uniform_H R (Finset.mem_filter.mp hR).1,(Finset.mem_filter.mp hR).2] at hp
    omega
  have hd : Disjoint (R \ M.O) (S ∩ support D.left) :=
    hRS.mono Finset.sdiff_subset Finset.inter_subset_left
  have hleft : (R \ M.O) ∪ (S ∩ support D.left) ∈ D.left := heH ▸ hm.1
  have hc := D.left_uniform _ hleft
  rw [Finset.card_union_of_disjoint hd,hP2] at hc
  exact ⟨by omega,heK ▸ hm.2.1,hleft⟩

theorem same_side_completion_right_card (R S : Finset α)
    (hR : R ∈ M.rows 2) (hS : S ∈ M.rows 0) (hRS : Disjoint R S)
    (hside : R \ M.O ⊆ support D.left) :
    (S ∩ support D.right).card = 3 :=
  D.right_uniform _ (D.same_side_completion R S hR hS hRS hside).2.1

/-- Pointwise form of the same-side completion, retaining the extension
membership and the synchronized opposite-side design tail. -/
theorem same_side_completion_point (R S : Finset α)
    (hR : R ∈ M.rows 2) (hS : S ∈ M.rows 0) (hRS : Disjoint R S)
    (hside : R \ M.O ⊆ support D.left) :
    ∃ a, S ∩ support D.left = {a} ∧
      a ∈ support D.left ∧ a ∉ R \ M.O ∧
      insert a (R \ M.O) ∈ D.left ∧
      S ∩ support D.right ∈ D.right ∧
      S = insert a (S ∩ support D.right) := by
  obtain ⟨h1,hK,hH⟩ := D.same_side_completion R S hR hS hRS hside
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp h1
  have ham : a ∈ S ∩ support D.left := by rw [ha]; simp
  have han : a ∉ R \ M.O :=
    fun h => Finset.disjoint_left.mp hRS (Finset.sdiff_subset h) (Finset.mem_inter.mp ham).1
  have hmem : insert a (R \ M.O) ∈ D.left := by
    rw [ha] at hH
    simpa only [Finset.union_singleton] using hH
  refine ⟨a,ha,(Finset.mem_inter.mp ham).2,han,hmem,hK,?_⟩
  have he := D.completion_union R S hR hS hRS
  rw [ha] at he
  simpa only [Finset.singleton_union] using he

/-- The center cannot occur in either residual design support. -/
theorem center_not_mem_left_support : M.x ∉ support D.left := by
  intro hx
  obtain ⟨T,hT,hxT⟩ := Finset.mem_biUnion.mp hx
  have hL : T ∈ residualLink M.F {M.x} := by
    rw [D.link_eq]
    exact Finset.mem_union_left _ hT
  have hd := residualLink_member_disjoint_core hL
  exact Finset.disjoint_left.mp hd (by simp) hxT

theorem center_not_mem_right_support : M.x ∉ support D.right :=
  D.swap.center_not_mem_left_support

end DesignPair
end FrontierProfileASplit
