import SunflowerLean.Erdos20SharpTwenty

/-! Support restrictions for extremal twenty-member triple families. -/
namespace Erdos20ExtremalSupport
open Erdos20BCWConditional Erdos20Incidence Erdos20RankThreeEven Erdos20SharpTwenty

/-- The supported points whose degree attains the graph-link ceiling six. -/
def degreeSixPoints {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Finset α :=
  (support F).filter (fun x => (F.filter (fun S => x ∈ S)).card = 6)

/-- Each member of a twenty-member family contains at most one degree-six point. -/
theorem extremal_member_saturated_card_le_one
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (hc : F.card = 20)
    (S : Finset α) (hS : S ∈ F) : (S ∩ degreeSixPoints F).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  obtain ⟨hxS,hxB⟩ := Finset.mem_inter.mp hx
  obtain ⟨hyS,hyB⟩ := Finset.mem_inter.mp hy
  have hpair : ({x,y} : Finset α) ⊆ S := by simp [Finset.insert_subset_iff,hxS,hyS]
  have hdiff : (S \ {x,y}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hpair,hu S hS]
    simp [hxy]
  obtain ⟨z,hz⟩ := Finset.card_eq_one.mp hdiff
  have hshape : S = {x,y,z} := by
    have he := Finset.union_sdiff_of_subset hpair
    rw [hz] at he
    have hu' : ({x,y} : Finset α) ∪ {z} = {x,y,z} := by ext t; simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]; tauto
    exact he.symm.trans hu'
  have hxdeg : (F.filter (fun T => x ∈ T)).card = 6 := (Finset.mem_filter.mp hxB).2
  have hydeg : (F.filter (fun T => y ∈ T)).card = 6 := (Finset.mem_filter.mp hyB).2
  have h19 := card_le_nineteen_of_two_degree_six_vertices F x y z hu hf
    (by simpa [hshape] using hS) hxdeg hydeg
  omega

/-- At most three points attain degree six in an extremal family. -/
theorem extremal_degree_six_points_card_le_three
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (hc : F.card = 20) :
    (degreeSixPoints F).card ≤ 3 := by
  have he := incidence_sum_eq F (degreeSixPoints F)
  have hlo : (∑ S ∈ F, (S ∩ degreeSixPoints F).card) ≤ 20 := by
    calc
      _ ≤ ∑ _S ∈ F, 1 := Finset.sum_le_sum (fun S hS => extremal_member_saturated_card_le_one F hu hf hc S hS)
      _ = 20 := by simp [hc]
  have hr : (∑ x ∈ degreeSixPoints F, (F.filter (fun S => x ∈ S)).card) =
      (degreeSixPoints F).card * 6 := by
    calc
      _ = ∑ _x ∈ degreeSixPoints F, 6 := Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2)
      _ = _ := by simp
  rw [he,hr] at hlo
  omega

/-- Counting incidences over the support recovers rank times family size. -/
theorem support_degree_sum
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (r : ℕ)
    (hu : ∀ S ∈ F, S.card = r) :
    (∑ x ∈ support F, (F.filter (fun S => x ∈ S)).card) = F.card * r := by
  rw [← incidence_sum_eq]
  calc
    _ = ∑ _S ∈ F, r := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.inter_eq_left.mpr (member_subset_support hS),hu S hS]
    _ = _ := by simp

/-- Every supported point of an extremal family has degree at least three. -/
theorem extremal_supported_degree_ge_three
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (hc : F.card = 20)
    (x : α) (hx : x ∈ support F) : 3 ≤ (F.filter (fun S => x ∈ S)).card := by
  obtain ⟨R,hR,hxR⟩ := Finset.mem_biUnion.mp hx
  have hh := rank_three_card_le_degree_add_seventeen F R x hR hxR hu hf
  omega

/-- An extremal twenty-member family uses between twelve and twenty points. -/
theorem extremal_support_card_window
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (hc : F.card = 20) :
    12 ≤ (support F).card ∧ (support F).card ≤ 20 := by
  classical
  have hsum : (∑ x ∈ support F, (F.filter (fun S => x ∈ S)).card) = 60 := by
    simpa [hc] using support_degree_sum F 3 hu
  have hB := extremal_degree_six_points_card_le_three F hu hf hc
  have hsumlo : (support F).card * 3 ≤ 60 := by
    calc
      _ = ∑ _x ∈ support F, 3 := by simp
      _ ≤ ∑ x ∈ support F, (F.filter (fun S => x ∈ S)).card :=
        Finset.sum_le_sum (fun x hx => extremal_supported_degree_ge_three F hu hf hc x hx)
      _ = 60 := hsum
  have hdf : ∀ x ∈ support F, (F.filter (fun S => x ∈ S)).card ≤
      5 + if x ∈ degreeSixPoints F then 1 else 0 := by
    intro x hx
    have hd := rank_three_degree_le_six F hu hf x
    by_cases hb : x ∈ degreeSixPoints F
    · simp [hb]; omega
    · have hdne : (F.filter (fun S => x ∈ S)).card ≠ 6 := by
        intro he
        exact hb (Finset.mem_filter.mpr ⟨hx,he⟩)
      simp [hb]; omega
  have hsumB : (∑ x ∈ support F, if x ∈ degreeSixPoints F then 1 else 0) =
      (degreeSixPoints F).card := by
    rw [← Finset.sum_filter]
    have he : (support F).filter (fun x => x ∈ degreeSixPoints F) = degreeSixPoints F := by
      ext x
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2,fun h => ⟨(Finset.mem_filter.mp h).1,h⟩⟩
    simp [he]
  have hsumhi : 60 ≤ (support F).card * 5 + (degreeSixPoints F).card := by
    calc
      60 = ∑ x ∈ support F, (F.filter (fun S => x ∈ S)).card := hsum.symm
      _ ≤ ∑ x ∈ support F, (5 + if x ∈ degreeSixPoints F then 1 else 0) := Finset.sum_le_sum hdf
      _ = _ := by rw [Finset.sum_add_distrib,hsumB]; simp
  constructor <;> omega

end Erdos20ExtremalSupport
