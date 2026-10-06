import SunflowerLean.Erdos20Incidence
import SunflowerLean.Erdos20TraceStructure

/-! Elementary bounds for intersecting and cross-intersecting trace classes. -/
namespace Erdos20CrossBounds

open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence

/-- A nonempty intersecting uniform family gains the full incidence defect of
one of its members. This statement has no sunflower assumption. -/
theorem intersecting_card_add_rank_sub_one_le
    {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (r B : ℕ)
    (hne : family.Nonempty)
    (huniform : ∀ S ∈ family, S.card = r)
    (hinter : ∀ S ∈ family, ∀ T ∈ family, (S ∩ T).Nonempty)
    (hdegree : ∀ x, (family.filter (fun S => x ∈ S)).card ≤ B) :
    family.card + (r - 1) ≤ r * B := by
  classical
  obtain ⟨R, hR⟩ := hne
  have hlo := incidence_defect_lower_bound family {R} R r
    (by simpa using hR)
    (by simpa using huniform R hR)
    (by simp) (fun S hS => hinter S hS R hR)
  have hsum : (∑ x ∈ R, (family.filter (fun S => x ∈ S)).card) ≤ r * B := by
    calc
      _ ≤ ∑ _x ∈ R, B := Finset.sum_le_sum (fun x _ => hdegree x)
      _ = _ := by simp [huniform R hR]
  simpa using hlo.trans hsum

/-- Rank-two three-sunflower-free families have degree at most two. -/
theorem rank_two_three_petals_degree_le_two
    {α : Type*} [DecidableEq α] (family : Finset (Finset α))
    (huniform : ∀ S ∈ family, S.card = 2)
    (hfree : IsSunflowerFree family 3) (x : α) :
    (family.filter (fun S => x ∈ S)).card ≤ 2 := by
  have hb := refined_sunflower_bound (residualLink family {x}) 1 3 (by decide)
    (by simpa using (residualLink_uniform (core := {x}) huniform))
    (residualLink_sunflowerFree hfree)
  simpa [refinedBound, card_residualLink, upperStar] using hb

/-- An intersecting graph with no three-petal sunflower has at most three edges. -/
theorem intersecting_rank_two_three_petals_card_le_three
    {α : Type*} [DecidableEq α] (family : Finset (Finset α))
    (huniform : ∀ S ∈ family, S.card = 2)
    (hfree : IsSunflowerFree family 3)
    (hinter : ∀ S ∈ family, ∀ T ∈ family, (S ∩ T).Nonempty) :
    family.card ≤ 3 := by
  by_cases hne : family.Nonempty
  · have hb := intersecting_card_add_rank_sub_one_le family 2 2 hne huniform hinter
      (rank_two_three_petals_degree_le_two family huniform hfree)
    omega
  · have he : family = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [he]

/-- A common point restricts a sunflower-free graph to at most two edges. -/
theorem common_point_rank_two_three_petals_card_le_two
    {α : Type*} [DecidableEq α] (family : Finset (Finset α))
    (huniform : ∀ S ∈ family, S.card = 2)
    (hfree : IsSunflowerFree family 3) (x : α)
    (hcommon : ∀ S ∈ family, x ∈ S) : family.card ≤ 2 := by
  have heq : family.filter (fun S => x ∈ S) = family := by
    apply Finset.filter_eq_self.mpr
    exact hcommon
  have hb := rank_two_three_petals_degree_le_two family huniform hfree x
  simpa [heq] using hb

/-- A fixed set that meets every member is a transversal; its cardinality
multiplied by the degree ceiling bounds the family. -/
theorem cross_intersecting_card_le
    {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (T : Finset α) (B : ℕ)
    (hcross : ∀ S ∈ family, (S ∩ T).Nonempty)
    (hdegree : ∀ x, (family.filter (fun S => x ∈ S)).card ≤ B) :
    family.card ≤ T.card * B := by
  classical
  have hlo := incidence_defect_lower_bound family ∅ T 0 (by simp)
    (by simp) (by simp) hcross
  have hsum : (∑ x ∈ T, (family.filter (fun S => x ∈ S)).card) ≤ T.card * B := by
    calc
      _ ≤ ∑ _x ∈ T, B := Finset.sum_le_sum (fun x _ => hdegree x)
      _ = _ := by simp
  simpa using hlo.trans hsum

/-- If a nonempty rank-two family cross-intersects a sunflower-free graph,
the latter graph has at most four edges. -/
theorem cross_intersecting_rank_two_card_le_four
    {α : Type*} [DecidableEq α] (family other : Finset (Finset α))
    (huniform : ∀ S ∈ family, S.card = 2)
    (hfree : IsSunflowerFree family 3)
    (hother : ∀ T ∈ other, T.card = 2) (hne : other.Nonempty)
    (hcross : ∀ S ∈ family, ∀ T ∈ other, (S ∩ T).Nonempty) :
    family.card ≤ 4 := by
  obtain ⟨T, hT⟩ := hne
  have hb := cross_intersecting_card_le family T 2 (fun S hS => hcross S hS T hT)
    (rank_two_three_petals_degree_le_two family huniform hfree)
  simpa [hother T hT] using hb

/-- For two intersecting distinct graph edges, a cross-intersecting graph
has at most one edge avoiding their common point. -/
theorem card_le_degree_add_one_of_two_intersecting_edges
    {α : Type*} [DecidableEq α] (family : Finset (Finset α))
    (B C : Finset α) (d : ℕ)
    (huniform : ∀ S ∈ family, S.card = 2)
    (hdegree : ∀ x, (family.filter (fun S => x ∈ S)).card ≤ d)
    (hB : B.card = 2) (hC : C.card = 2) (hne : B ≠ C)
    (hBC : (B ∩ C).Nonempty)
    (hcrossB : ∀ S ∈ family, (S ∩ B).Nonempty)
    (hcrossC : ∀ S ∈ family, (S ∩ C).Nonempty) :
    family.card ≤ d + 1 := by
  classical
  obtain ⟨x, hx⟩ := hBC
  obtain ⟨hxB, hxC⟩ := Finset.mem_inter.mp hx
  have heB : (B.erase x).card = 1 := by rw [Finset.card_erase_of_mem hxB, hB]
  have heC : (C.erase x).card = 1 := by rw [Finset.card_erase_of_mem hxC, hC]
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp heB
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp heC
  have hBshape : B = {x, y} := by rw [← Finset.insert_erase hxB, hy]
  have hCshape : C = {x, z} := by rw [← Finset.insert_erase hxC, hz]
  have hyz : y ≠ z := by intro he; apply hne; rw [hBshape, hCshape, he]
  have hcover : family ⊆ (family.filter (fun S => x ∈ S)) ∪ {{y, z}} := by
    intro S hS
    by_cases hxS : x ∈ S
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hS, hxS⟩)
    · have hyS : y ∈ S := by
        obtain ⟨w, hw⟩ := hcrossB S hS
        obtain ⟨hwS, hwB⟩ := Finset.mem_inter.mp hw
        rw [hBshape] at hwB
        rcases Finset.mem_insert.mp hwB with hwx | hwy
        · exact False.elim (hxS (hwx ▸ hwS))
        · exact (Finset.mem_singleton.mp hwy) ▸ hwS
      have hzS : z ∈ S := by
        obtain ⟨w, hw⟩ := hcrossC S hS
        obtain ⟨hwS, hwC⟩ := Finset.mem_inter.mp hw
        rw [hCshape] at hwC
        rcases Finset.mem_insert.mp hwC with hwx | hwz
        · exact False.elim (hxS (hwx ▸ hwS))
        · exact (Finset.mem_singleton.mp hwz) ▸ hwS
      have hpair : ({y, z} : Finset α) ⊆ S := by simpa [Finset.insert_subset_iff] using And.intro hyS hzS
      have heq : {y, z} = S := Finset.eq_of_subset_of_card_le hpair
        (by simp [huniform S hS, hyz])
      exact Finset.mem_union_right _ (by simpa using heq.symm)
  calc
    family.card ≤ ((family.filter (fun S => x ∈ S)) ∪ {{y, z}}).card :=
      Finset.card_le_card hcover
    _ ≤ (family.filter (fun S => x ∈ S)).card + ({{y, z}} : Finset (Finset α)).card :=
      Finset.card_union_le _ _
    _ ≤ d + 1 := by simpa using Nat.add_le_add_right (hdegree x) 1

/-- If one side has at least four edges, a cross-intersecting sunflower-free
graph on the other side must be a matching. -/
theorem cross_intersecting_large_forces_matching
    {α : Type*} [DecidableEq α] (family other : Finset (Finset α))
    (huniform : ∀ S ∈ family, S.card = 2)
    (hfree : IsSunflowerFree family 3)
    (hother : ∀ T ∈ other, T.card = 2)
    (hlarge : 4 ≤ family.card)
    (hcross : ∀ S ∈ family, ∀ T ∈ other, (S ∩ T).Nonempty) :
    IsPairwiseDisjoint other := by
  intro B C hB hC hne
  by_contra hnot
  have hBC : (B ∩ C).Nonempty := Finset.nonempty_iff_ne_empty.mpr hnot
  have hb := card_le_degree_add_one_of_two_intersecting_edges family B C 2
    huniform (rank_two_three_petals_degree_le_two family huniform hfree)
    (hother B hB) (hother C hC) hne hBC
    (fun S hS => hcross S hS B hB) (fun S hS => hcross S hS C hC)
  omega

/-- Four or more edges on one side force at most two on the other. -/
theorem cross_intersecting_large_other_card_le_two
    {α : Type*} [DecidableEq α] (family other : Finset (Finset α))
    (huniform : ∀ S ∈ family, S.card = 2)
    (hfree : IsSunflowerFree family 3)
    (hother : ∀ T ∈ other, T.card = 2)
    (hotherfree : IsSunflowerFree other 3) (hlarge : 4 ≤ family.card)
    (hcross : ∀ S ∈ family, ∀ T ∈ other, (S ∩ T).Nonempty) :
    other.card ≤ 2 := by
  have hdis := cross_intersecting_large_forces_matching family other huniform hfree
    hother hlarge hcross
  have hb := Erdos20Classical.pairwiseDisjoint_card_lt_forbidden
    other other 3 (Finset.Subset.refl _) hdis hotherfree
  omega

/-- Two cross-intersecting, three-sunflower-free graphs have at most six
edges in total; the sides need not be disjoint as families. -/
theorem cross_intersecting_rank_two_joint_card_le_six
    {α : Type*} [DecidableEq α] (family other : Finset (Finset α))
    (huniform : ∀ S ∈ family, S.card = 2)
    (hfree : IsSunflowerFree family 3)
    (hother : ∀ T ∈ other, T.card = 2)
    (hotherfree : IsSunflowerFree other 3)
    (hcross : ∀ S ∈ family, ∀ T ∈ other, (S ∩ T).Nonempty) :
    family.card + other.card ≤ 6 := by
  by_cases hF : family.Nonempty
  · by_cases hG : other.Nonempty
    · have hA4 := cross_intersecting_rank_two_card_le_four
        family other huniform hfree hother hG hcross
      have hsym : ∀ T ∈ other, ∀ S ∈ family, (T ∩ S).Nonempty := by
        intro T hT S hS
        simpa [Finset.inter_comm] using hcross S hS T hT
      have hB4 := cross_intersecting_rank_two_card_le_four
        other family hother hotherfree huniform hF hsym
      by_cases hA3 : family.card ≤ 3
      · by_cases hB3 : other.card ≤ 3
        · omega
        · have hb := cross_intersecting_large_other_card_le_two
            other family hother hotherfree huniform hfree (by omega) hsym
          omega
      · have hb := cross_intersecting_large_other_card_le_two
          family other huniform hfree hother hotherfree (by omega) hcross
        omega
    · have he : other = ∅ := Finset.not_nonempty_iff_eq_empty.mp hG
      simpa [he] using rank_two_three_petals_card_le_six family huniform hfree
  · have he : family = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simpa [he] using rank_two_three_petals_card_le_six other hother hotherfree

/-- The triangle on the first three points of the existing six-point witness. -/
def jointSharpTriangle : Finset (Finset (Fin 6)) :=
  {{0, 1}, {0, 2}, {1, 2}}

/-- The joint bound six is attained by taking a triangle on each side. -/
theorem cross_intersecting_joint_bound_sharp :
    (∀ S ∈ jointSharpTriangle, S.card = 2) ∧
    IsSunflowerFree jointSharpTriangle 3 ∧
    (∀ S ∈ jointSharpTriangle, ∀ T ∈ jointSharpTriangle, (S ∩ T).Nonempty) ∧
    jointSharpTriangle.card + jointSharpTriangle.card = 6 := by
  refine ⟨by decide, ?_, by decide, by decide⟩
  intro F hF hsun
  exact twoTriangles_sunflower_free F
    (hF.trans (by decide : jointSharpTriangle ⊆ twoTriangles)) hsun

end Erdos20CrossBounds
