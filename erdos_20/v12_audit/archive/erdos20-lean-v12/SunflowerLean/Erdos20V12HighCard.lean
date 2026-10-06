import SunflowerLean.Erdos20V12HighEdge

namespace Erdos20V12HighCard
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20V8Boundary Erdos20DegreeCongruences Erdos20V9HighGraph
open Erdos20V11HighSupport Erdos20V12HighEdge

/-- Every three distinct high points are pairwise nonadjacent. -/
theorem three_high_pairwise_nonadjacent {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x y z : α) (hx : x ∈ highPoints F) (hy : y ∈ highPoints F)
    (hz : z ∈ highPoints F) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    y ∉ highNeighbors F x ∧ z ∉ highNeighbors F x ∧ z ∉ highNeighbors F y := by
  refine ⟨?_,?_,?_⟩
  · intro hN
    exact high_edge_excludes_third_high F hu hf x hx y hN z hz hxz hyz
  · intro hN
    exact high_edge_excludes_third_high F hu hf x hx z hN y hy hxy (Ne.symm hyz)
  · intro hN
    exact high_edge_excludes_third_high F hu hf y hy z hN x hx (Ne.symm hxy) (Ne.symm hxz)

/-- The original family has at most three degree-twenty points. This statement
is unconditional in the intersecting ceiling, family size and support size. -/
theorem high_points_card_le_three {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3) :
    (highPoints F).card ≤ 3 := by
  by_contra hn
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ := Finset.two_lt_card_iff.mp
    (show 2<(highPoints F).card by omega)
  obtain ⟨hyNx,hzNx,hzNy⟩ := three_high_pairwise_nonadjacent F hu hf x y z hx hy hz hxy hxz hyz
  have he := independent_high_triple_exhausts_high_class F hu hf x y z hx hy hz hxy hxz hyz hyNx hzNx hzNy
  have hc : (highPoints F).card=3 := by rw [he]; simp [hxy,hxz,hyz]
  omega

/-- If there are at least three high points, they are exactly three and share
one twelve-point entirely low residual support; every original member uses at
most one high point. All sets in this conclusion are actual family supports. -/
theorem three_high_common_support_structure {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (hc : 3 ≤ (highPoints F).card) :
    (highPoints F).card=3 ∧ ∃ N : Finset α, N.card=12 ∧ Disjoint N (highPoints F) ∧
      (∀ w ∈ highPoints F, support (residualLink F {w})=N) ∧
      (∀ R ∈ F, (R ∩ highPoints F).card≤1) := by
  have hb := high_points_card_le_three F hu hf
  refine ⟨by omega,?_⟩
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ := Finset.two_lt_card_iff.mp
    (show 2<(highPoints F).card by omega)
  obtain ⟨hyNx,hzNx,hzNy⟩ := three_high_pairwise_nonadjacent F hu hf x y z hx hy hz hxy hxz hyz
  have hd := common_high_support_disjoint_high F hu hf x y z hx hy hz hxy hxz hyz hyNx hzNx hzNy
  have hS := all_high_supports_eq_of_independent_triple F hu hf x y z hx hy hz hxy hxz hyz hyNx hzNx hzNy
  exact ⟨support (residualLink F {z}),(high_link_twenty_and_support_twelve F hu hf z hz).2,
    hd,hS,member_high_cap_one_of_common_support F _ hS hd⟩

end Erdos20V12HighCard
