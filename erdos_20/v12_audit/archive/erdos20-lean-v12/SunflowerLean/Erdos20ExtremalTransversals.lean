import SunflowerLean.Erdos20ExtremalTwenty
import SunflowerLean.Erdos20RankFour

/-! Sharp transversal size for extremal triple families and saturated rank-four links. -/
namespace Erdos20ExtremalTransversals
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence Erdos20CrossBounds
open Erdos20ExtremalTwenty Erdos20DesignSeparation Erdos20V5Frontier Erdos20RankFour

/-- Every transversal of an intersecting ten-triple family has at least three points. -/
theorem intersecting_ten_transversal_card_ge_three
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 10)
    (C : Finset α) (hhit : ∀ S ∈ F, (S ∩ C).Nonempty) : 3 ≤ C.card := by
  have hd : ∀ x, (F.filter (fun S => x ∈ S)).card ≤ 5 :=
    Erdos20ExtremalStructure.intersecting_card_ge_seven_degree_le_five F hu hf hi (by omega)
  have hlow := cross_intersecting_card_le F C 5 hhit hd
  by_contra hn
  have hC : C.card = 2 := by omega
  obtain ⟨S,hS,hdis⟩ := intersecting_ten_no_two_point_transversal F hu hf hi hc C hC
  have hh := hhit S hS
  rw [hdis] at hh
  exact Finset.not_nonempty_empty hh

/-- A transversal restricted to the support of a subfamily still meets that subfamily. -/
theorem transversal_restrict_support
    {α : Type*} [DecidableEq α] (F H : Finset (Finset α)) (C : Finset α)
    (hHF : H ⊆ F) (hhit : ∀ S ∈ F, (S ∩ C).Nonempty) :
    ∀ S ∈ H, (S ∩ (C ∩ support H)).Nonempty := by
  intro S hS
  obtain ⟨x,hx⟩ := hhit S (hHF hS)
  obtain ⟨hxS,hxC⟩ := Finset.mem_inter.mp hx
  exact ⟨x,Finset.mem_inter.mpr ⟨hxS,Finset.mem_inter.mpr
    ⟨hxC,member_subset_support hS hxS⟩⟩⟩

/-- Every transversal of an extremal twenty-triple family has at least six points. -/
theorem extremal_twenty_transversal_card_ge_six
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (hc : F.card = 20)
    (C : Finset α) (hhit : ∀ S ∈ F, (S ∩ C).Nonempty) : 6 ≤ C.card := by
  classical
  obtain ⟨H,hHF,hHc,hHi⟩ := extremal_twenty_contains_intersecting_ten F hu hf hc
  obtain ⟨hKc,hKi,hdis,_,_,_⟩ :=
    extremal_twenty_complement_design F H hu hf hHF hHi hHc hc
  have hHf : IsSunflowerFree H 3 := fun G hG hg => hf G (hG.trans hHF) hg
  have hKf : IsSunflowerFree (F \ H) 3 := fun G hG hg => hf G (hG.trans Finset.sdiff_subset) hg
  have hH := intersecting_ten_transversal_card_ge_three H
    (fun S hS => hu S (hHF hS)) hHf hHi hHc (C ∩ support H)
    (transversal_restrict_support F H C hHF hhit)
  have hK := intersecting_ten_transversal_card_ge_three (F \ H)
    (fun S hS => hu S (Finset.mem_sdiff.mp hS).1) hKf hKi hKc (C ∩ support (F \ H))
    (transversal_restrict_support F (F \ H) C Finset.sdiff_subset hhit)
  have hd : Disjoint (C ∩ support H) (C ∩ support (F \ H)) :=
    hdis.mono Finset.inter_subset_right Finset.inter_subset_right
  have hsub : (C ∩ support H) ∪ (C ∩ support (F \ H)) ⊆ C :=
    Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd] at hcard
  omega

/-- Every set of at most five points misses a member of an extremal twenty-triple family. -/
theorem extremal_twenty_avoids_five_points
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (hc : F.card = 20)
    (C : Finset α) (hC : C.card ≤ 5) : ∃ S ∈ F, S ∩ C = ∅ := by
  classical
  by_contra hn
  push_neg at hn
  have hlow := extremal_twenty_transversal_card_ge_six F hu hf hc C hn
  omega

/-- A minimum transversal is the union of one member from each of the two components. -/
theorem extremal_twenty_exists_transversal_six
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (hc : F.card = 20) :
    ∃ R ∈ F, ∃ T ∈ F, Disjoint R T ∧ (R ∪ T).card = 6 ∧
      ∀ S ∈ F, (S ∩ (R ∪ T)).Nonempty := by
  classical
  obtain ⟨H,hHF,hHc,hHi⟩ := extremal_twenty_contains_intersecting_ten F hu hf hc
  obtain ⟨hKc,hKi,hdis,_,_,_⟩ :=
    extremal_twenty_complement_design F H hu hf hHF hHi hHc hc
  obtain ⟨R,hRH⟩ := Finset.card_pos.mp (show 0 < H.card by omega)
  obtain ⟨T,hTK⟩ := Finset.card_pos.mp (show 0 < (F \ H).card by omega)
  have hRF : R ∈ F := hHF hRH
  have hTF : T ∈ F := (Finset.mem_sdiff.mp hTK).1
  have hd : Disjoint R T := hdis.mono (member_subset_support hRH) (member_subset_support hTK)
  refine ⟨R,hRF,T,hTF,hd,?_,?_⟩
  · rw [Finset.card_union_of_disjoint hd,hu R hRF,hu T hTF]
  · intro S hSF
    by_cases hSH : S ∈ H
    · obtain ⟨x,hx⟩ := hHi S hSH R hRH
      obtain ⟨hxS,hxR⟩ := Finset.mem_inter.mp hx
      exact ⟨x,Finset.mem_inter.mpr ⟨hxS,Finset.mem_union_left _ hxR⟩⟩
    · obtain ⟨x,hx⟩ := hKi S (Finset.mem_sdiff.mpr ⟨hSF,hSH⟩) T hTK
      obtain ⟨hxS,hxT⟩ := Finset.mem_inter.mp hx
      exact ⟨x,Finset.mem_inter.mpr ⟨hxS,Finset.mem_union_right _ hxT⟩⟩

/-- A degree-twenty point in an intersecting rank-four family belongs to every member. -/
theorem intersecting_rank_four_degree_twenty_common_point
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (x : α) (hd : (F.filter (fun S => x ∈ S)).card = 20) :
    ∀ T ∈ F, x ∈ T := by
  classical
  let L := residualLink F {x}
  have hLu : ∀ S ∈ L, S.card = 3 := by
    simpa [L] using residualLink_uniform (core := {x}) hu
  have hLf : IsSunflowerFree L 3 := residualLink_sunflowerFree hf
  have hLc : L.card = 20 := by simpa [L,card_residualLink,upperStar] using hd
  intro T hT
  by_contra hxT
  have hhit : ∀ P ∈ L, (P ∩ T).Nonempty := by
    intro P hP
    have hPF : {x} ∪ P ∈ F := core_union_residual_mem_family hP
    obtain ⟨y,hy⟩ := hi ({x} ∪ P) hPF T hT
    obtain ⟨hyP,hyT⟩ := Finset.mem_inter.mp hy
    rcases Finset.mem_union.mp hyP with hyx | hyP
    · have he : y = x := Finset.mem_singleton.mp hyx
      exact False.elim (hxT (he ▸ hyT))
    · exact ⟨y,Finset.mem_inter.mpr ⟨hyP,hyT⟩⟩
  have hlow := extremal_twenty_transversal_card_ge_six L hLu hLf hLc T hhit
  rw [hu T hT] at hlow
  omega

/-- A saturated point forces cardinality exactly twenty in the intersecting rank-four case. -/
theorem intersecting_rank_four_degree_twenty_card_eq_twenty
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (x : α) (hd : (F.filter (fun S => x ∈ S)).card = 20) : F.card = 20 := by
  have he : F.filter (fun S => x ∈ S) = F :=
    Finset.filter_eq_self.mpr (intersecting_rank_four_degree_twenty_common_point F hu hf hi x hd)
  rwa [he] at hd

/-- Every point degree is at most nineteen once an intersecting rank-four family has at least twenty-one members. -/
theorem intersecting_rank_four_card_ge_twenty_one_degree_le_nineteen
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : 21 ≤ F.card)
    (x : α) : (F.filter (fun S => x ∈ S)).card ≤ 19 := by
  have hd := rank_four_degree_le_twenty F hu hf x
  by_contra hn
  have he := intersecting_rank_four_degree_twenty_card_eq_twenty F hu hf hi x (by omega)
  omega

end Erdos20ExtremalTransversals
