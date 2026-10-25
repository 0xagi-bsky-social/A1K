import SunflowerLean.Erdos20V5Frontier

/-! A ten-member intersecting triple design is an isolated component in every
three-sunflower-free triple family containing it. -/
namespace Erdos20DesignSeparation
open Erdos20BCWConditional Erdos20MixedCross Erdos20RankThree Erdos20V5Frontier

/-- An outside member cannot contain two supported points of an intersecting
extremal triple subfamily: all those pairs already have saturated codegree. -/
theorem outside_intersecting_ten_no_supported_pair
    {α : Type*} [DecidableEq α] (F H : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (hHF : H ⊆ F)
    (hi : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty) (hc : H.card = 10)
    (T : Finset α) (hTF : T ∈ F) (hTH : T ∉ H)
    (x y : α) (hx : x ∈ support H) (hy : y ∈ support H)
    (hxT : x ∈ T) (hyT : y ∈ T) : x = y := by
  classical
  by_contra hxy
  have hHf : IsSunflowerFree H 3 := fun G hG hg => hf G (hG.trans hHF) hg
  obtain ⟨_,_,hp⟩ := intersecting_ten_design H (fun S hS => hu S (hHF hS)) hHf hi hc
  have htwo := hp x hx y hy hxy
  let P := H.filter (fun S => ({x,y} : Finset α) ⊆ S)
  have hTP : T ∉ P := fun h => hTH (Finset.mem_filter.mp h).1
  have hsub : insert T P ⊆ F.filter (fun S => ({x,y} : Finset α) ⊆ S) := by
    intro S hS
    rcases Finset.mem_insert.mp hS with rfl | hS
    · exact Finset.mem_filter.mpr ⟨hTF,by simp [Finset.insert_subset_iff,hxT,hyT]⟩
    · obtain ⟨hSH,hpair⟩ := Finset.mem_filter.mp hS
      exact Finset.mem_filter.mpr ⟨hHF hSH,hpair⟩
  have hle := Finset.card_le_card hsub
  have hcap := triple_pair_degree_le_two F hu hf {x,y} (by simp [hxy])
  have hP : P.card = 2 := htwo
  rw [Finset.card_insert_of_notMem hTP,hP] at hle
  omega

/-- Every member outside an intersecting ten-member triple subfamily is
entirely disjoint from its six-point support. -/
theorem outside_intersecting_ten_disjoint_support
    {α : Type*} [DecidableEq α] (F H : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (hHF : H ⊆ F)
    (hi : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty) (hc : H.card = 10)
    (T : Finset α) (hTF : T ∈ F) (hTH : T ∉ H) :
    Disjoint T (support H) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxT hxH
  have hHf : IsSunflowerFree H 3 := fun G hG hg => hf G (hG.trans hHF) hg
  obtain ⟨_,hd,_⟩ := intersecting_ten_design H (fun S hS => hu S (hHF hS)) hHf hi hc
  have hsub : H.filter (fun S => x ∈ S) ⊆ exactTrace F T {x} := by
    intro S hS
    obtain ⟨hSH,hxS⟩ := Finset.mem_filter.mp hS
    refine Finset.mem_filter.mpr ⟨hHF hSH,?_⟩
    apply Finset.Subset.antisymm
    · intro y hy
      obtain ⟨hyS,hyT⟩ := Finset.mem_inter.mp hy
      exact Finset.mem_singleton.mpr (outside_intersecting_ten_no_supported_pair
        F H hu hf hHF hi hc T hTF hTH y x (member_subset_support hSH hyS) hxH hyT hxT)
    · intro y hy
      have he := Finset.mem_singleton.mp hy
      subst y
      exact Finset.mem_inter.mpr ⟨hxS,hxT⟩
  have hlo := Finset.card_le_card hsub
  have hcap := singleton_trace_card_le_three F T {x} hTF hu hf (by simp)
  have hxdeg := hd x hxH
  omega

/-- Once an intersecting ten-member component is present, all remaining
members intersect one another. -/
theorem complement_of_intersecting_ten_intersecting
    {α : Type*} [DecidableEq α] (F H : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (hHF : H ⊆ F)
    (hi : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty) (hc : H.card = 10) :
    ∀ S ∈ F \ H, ∀ T ∈ F \ H, (S ∩ T).Nonempty := by
  classical
  obtain ⟨R,hRH⟩ := Finset.card_pos.mp (show 0 < H.card by omega)
  have hRne : R.Nonempty := Finset.card_pos.mp (by rw [hu R (hHF hRH)]; decide)
  have hdis : ∀ S ∈ F \ H, S ∩ R = ∅ := by
    intro S hS
    obtain ⟨hSF,hSH⟩ := Finset.mem_sdiff.mp hS
    apply Finset.disjoint_iff_inter_eq_empty.mp
    exact (outside_intersecting_ten_disjoint_support F H hu hf hHF hi hc S hSF hSH).mono_right
      (member_subset_support hRH)
  intro S hS T hT
  have hSF := (Finset.mem_sdiff.mp hS).1
  have hTF := (Finset.mem_sdiff.mp hT).1
  exact disjoint_anchor_family_intersecting F R (hHF hRH) hRne hf S
    (Finset.mem_filter.mpr ⟨hSF,hdis S hS⟩) T
    (Finset.mem_filter.mpr ⟨hTF,hdis T hT⟩)
    (Finset.card_pos.mp (by rw [hu S hSF]; decide))
    (Finset.card_pos.mp (by rw [hu T hTF]; decide))

/-- The complement of an intersecting ten-member component has at most ten
members, by the sharp intersecting bound. -/
theorem complement_of_intersecting_ten_card_le_ten
    {α : Type*} [DecidableEq α] (F H : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (hHF : H ⊆ F)
    (hi : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty) (hc : H.card = 10) :
    (F \ H).card ≤ 10 := by
  exact intersecting_rank_three_card_le_ten (F \ H)
    (fun S hS => hu S (Finset.mem_sdiff.mp hS).1)
    (fun G hG hg => hf G (hG.trans Finset.sdiff_subset) hg)
    (complement_of_intersecting_ten_intersecting F H hu hf hHF hi hc)

/-- The two component supports are disjoint, regardless of the size of the
complement. -/
theorem intersecting_ten_complement_supports_disjoint
    {α : Type*} [DecidableEq α] (F H : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (hHF : H ⊆ F)
    (hi : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty) (hc : H.card = 10) :
    Disjoint (support H) (support (F \ H)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxH hxD
  obtain ⟨S,hSD,hxS⟩ := Finset.mem_biUnion.mp hxD
  obtain ⟨hSF,hSH⟩ := Finset.mem_sdiff.mp hSD
  exact Finset.disjoint_left.mp
    (outside_intersecting_ten_disjoint_support F H hu hf hHF hi hc S hSF hSH) hxS hxH

/-- In an extremal twenty-member family, the complement of an intersecting
ten-member component is another intersecting ten-member six-point design. -/
theorem extremal_twenty_complement_design
    {α : Type*} [DecidableEq α] (F H : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (hHF : H ⊆ F)
    (hi : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty) (hc : H.card = 10)
    (hFcard : F.card = 20) :
    (F \ H).card = 10 ∧
    (∀ S ∈ F \ H, ∀ T ∈ F \ H, (S ∩ T).Nonempty) ∧
    Disjoint (support H) (support (F \ H)) ∧
    (support (F \ H)).card = 6 ∧
    (∀ x ∈ support (F \ H), ((F \ H).filter (fun S => x ∈ S)).card = 5) ∧
    (∀ x ∈ support (F \ H), ∀ y ∈ support (F \ H), x ≠ y →
      ((F \ H).filter (fun S => ({x,y} : Finset α) ⊆ S)).card = 2) := by
  classical
  have hDc : (F \ H).card = 10 := by rw [Finset.card_sdiff_of_subset hHF,hFcard,hc]
  have hDi := complement_of_intersecting_ten_intersecting F H hu hf hHF hi hc
  have hDu : ∀ S ∈ F \ H, S.card = 3 := fun S hS => hu S (Finset.mem_sdiff.mp hS).1
  have hDf : IsSunflowerFree (F \ H) 3 :=
    fun G hG hg => hf G (hG.trans Finset.sdiff_subset) hg
  exact ⟨hDc,hDi,intersecting_ten_complement_supports_disjoint F H hu hf hHF hi hc,
    intersecting_ten_design (F \ H) hDu hDf hDi hDc⟩

/-- The isolated ten-member component contributes the entire ambient degree
of each of its supported points. -/
theorem intersecting_ten_degrees_preserved
    {α : Type*} [DecidableEq α] (F H : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (hHF : H ⊆ F)
    (hi : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty) (hc : H.card = 10)
    (x : α) (hx : x ∈ support H) : (F.filter (fun S => x ∈ S)).card = 5 := by
  classical
  have hHf : IsSunflowerFree H 3 := fun G hG hg => hf G (hG.trans hHF) hg
  obtain ⟨_,hd,_⟩ := intersecting_ten_design H (fun S hS => hu S (hHF hS)) hHf hi hc
  have he : F.filter (fun S => x ∈ S) = H.filter (fun S => x ∈ S) := by
    ext S
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hSF,hxS⟩
      by_cases hSH : S ∈ H
      · exact ⟨hSH,hxS⟩
      · exact False.elim (Finset.disjoint_left.mp
          (outside_intersecting_ten_disjoint_support F H hu hf hHF hi hc S hSF hSH) hxS hx)
    · exact fun h => ⟨hHF h.1,h.2⟩
  rw [he]
  exact hd x hx

/-- Conditional on containing an intersecting ten-member subfamily, every
extremal twenty-member family has twelve supported points, all of degree five.
The existence of that subfamily is not asserted here. -/
theorem extremal_twenty_regular_twelve_of_intersecting_ten
    {α : Type*} [DecidableEq α] (F H : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (hHF : H ⊆ F)
    (hi : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty) (hc : H.card = 10)
    (hFcard : F.card = 20) :
    (support F).card = 12 ∧
    ∀ x ∈ support F, (F.filter (fun S => x ∈ S)).card = 5 := by
  classical
  obtain ⟨hDc,hDi,hdis,hDs,_,_⟩ :=
    extremal_twenty_complement_design F H hu hf hHF hi hc hFcard
  have hHf : IsSunflowerFree H 3 := fun G hG hg => hf G (hG.trans hHF) hg
  obtain ⟨hHs,_,_⟩ := intersecting_ten_design H (fun S hS => hu S (hHF hS)) hHf hi hc
  have he : support F = support H ∪ support (F \ H) := by
    ext x
    simp only [support,Finset.mem_biUnion,Finset.mem_union]
    constructor
    · rintro ⟨S,hSF,hxS⟩
      by_cases hSH : S ∈ H
      · exact Or.inl ⟨S,hSH,hxS⟩
      · exact Or.inr ⟨S,Finset.mem_sdiff.mpr ⟨hSF,hSH⟩,hxS⟩
    · rintro (⟨S,hSH,hxS⟩ | ⟨S,hSD,hxS⟩)
      · exact ⟨S,hHF hSH,hxS⟩
      · exact ⟨S,(Finset.mem_sdiff.mp hSD).1,hxS⟩
  refine ⟨by rw [he,Finset.card_union_of_disjoint hdis,hHs,hDs],?_⟩
  intro x hx
  rw [he] at hx
  rcases Finset.mem_union.mp hx with hxH | hxD
  · exact intersecting_ten_degrees_preserved F H hu hf hHF hi hc x hxH
  · exact intersecting_ten_degrees_preserved F (F \ H) hu hf Finset.sdiff_subset hDi hDc x hxD

end Erdos20DesignSeparation
