import TwoStarBridge
import TwoHighIncidence

namespace FrontierTwoHighEighty
open Erdos20BCWConditional Erdos20StrictCore Erdos20DegreeCongruences
open Erdos20V8Boundary FrontierTwoStarResidual FrontierTwoStarBridge
open FrontierTwoHighIncidence

variable {α : Type*} [DecidableEq α]

/-- Two independent extremal twenty-stars cannot extend past eighty members
when all other point degrees are at most nineteen. This theorem has no
ambient support-size assumption and no intersecting-family-bound premise. -/
theorem two_independent_high_card_le_eighty
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card = 4)
    (hf : IsSunflowerFree F 3) (x y : α)
    (hx : x ∈ highPoints F) (hy : y ∈ highPoints F)
    (hj : ∀ R ∈ F, ¬ (x ∈ R ∧ y ∈ R))
    (hd : ∀ v, v ≠ x → v ≠ y → degree F v ≤ 19) : F.card ≤ 80 := by
  let H := F.filter (fun R => x ∉ R ∧ y ∉ R)
  let U := support (residualLink F {x})
  let V := support (residualLink F {y})
  have hX := Erdos20V11HighSupport.high_link_twenty_and_support_twelve F hu hf x hx
  have hY := Erdos20V11HighSupport.high_link_twenty_and_support_twelve F hu hf y hy
  have hdegree := residual_degree_bounds F hu hf x y hx hy hj hd
  have h40 : H.card ≤ 40 := by
    apply two_large_supports_card_le_forty H U V
    · intro R hR; exact hu R (Finset.mem_filter.mp hR).1
    · exact hX.2
    · intro R hR
      obtain ⟨hRF,hxR,hyR⟩ := Finset.mem_filter.mp hR
      exact residual_meets_link_support_ge_three F hu hf x y hX.1 hY.1 hj R hRF hxR hyR
    · intro R hR
      obtain ⟨hRF,hxR,hyR⟩ := Finset.mem_filter.mp hR
      exact residual_meets_link_support_ge_three F hu hf y x hY.1 hX.1
        (fun R hR h => hj R hR ⟨h.2,h.1⟩) R hRF hyR hxR
    · exact hdegree.1
    · exact hdegree.2
  have hpart := two_star_partition F x y hj
  have hx20 : degree F x = 20 := (Finset.mem_filter.mp hx).2
  have hy20 : degree F y = 20 := (Finset.mem_filter.mp hy).2
  change H.card + degree F x + degree F y = F.card at hpart
  omega

/-- A degree-twenty point necessarily belongs to the high-point set. -/
theorem degree_twenty_mem_high (F : Finset (Finset α)) (v : α)
    (hv : degree F v = 20) : v ∈ highPoints F := by
  apply Finset.mem_filter.mpr
  refine ⟨?_,hv⟩
  have hp : 0 < (F.filter (fun R => v ∈ R)).card := by change 0 < degree F v; omega
  obtain ⟨R,hR⟩ := Finset.card_pos.mp hp
  exact member_subset_support (Finset.mem_filter.mp hR).1 (Finset.mem_filter.mp hR).2

/-- A four-uniform sunflower-free family with exactly two high points,
no member containing both, has at most eighty members. -/
theorem exactly_two_high_card_le_eighty
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card = 4)
    (hf : IsSunflowerFree F 3) (hhigh : (highPoints F).card = 2)
    (hcap : ∀ R ∈ F, (R ∩ highPoints F).card ≤ 1) : F.card ≤ 80 := by
  obtain ⟨x,y,hxy,hshape⟩ := Finset.card_eq_two.mp hhigh
  have hx : x ∈ highPoints F := by rw [hshape]; simp
  have hy : y ∈ highPoints F := by rw [hshape]; simp
  apply two_independent_high_card_le_eighty F hu hf x y hx hy
  · intro R hR hj
    have hsub : ({x,y} : Finset α) ⊆ R ∩ highPoints F := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Finset.mem_inter.mpr ⟨hj.1,hx⟩
      · have he : v = y := Finset.mem_singleton.mp hv
        subst v
        exact Finset.mem_inter.mpr ⟨hj.2,hy⟩
    have hb := Finset.card_le_card hsub
    have hc := hcap R hR
    simp only [Finset.card_pair hxy] at hb
    omega
  · intro v hvx hvy
    have hb := Erdos20RankFour.rank_four_degree_le_twenty F hu hf v
    change degree F v ≤ 20 at hb
    have hn : degree F v ≠ 20 := by
      intro he
      have hm := degree_twenty_mem_high F v he
      rw [hshape] at hm
      simpa only [Finset.mem_insert,Finset.mem_singleton,hvx,hvy,false_or] using hm
    omega

/-- Literal Profile B is excluded with no extra mathematical premise. -/
theorem profile_b_not_realizable : ¬ Erdos20V13Boundary.ProfileBRealizable := by
  classical
  rintro ⟨α,inst,F,hu,hf,h81,_,_,_,_,hh,hcap⟩
  letI := inst
  have hb := exactly_two_high_card_le_eighty F hu hf hh hcap
  omega

/-- Literal universal extension bound: two distinct degree-twenty centers
that never cooccur force at most eighty members. The bound on every other
point degree follows from the inherited unconditional two-high-point cap. -/
theorem independent_twenty_stars_card_le_eighty
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card = 4)
    (hf : IsSunflowerFree F 3) (x y : α) (hxy : x ≠ y)
    (hx20 : degree F x = 20) (hy20 : degree F y = 20)
    (hj : ∀ R ∈ F, ¬ (x ∈ R ∧ y ∈ R)) : F.card ≤ 80 := by
  have hx := degree_twenty_mem_high F x hx20
  have hy := degree_twenty_mem_high F y hy20
  have hpair : ({x,y} : Finset α) ⊆ highPoints F := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hx
    · simpa only [Finset.mem_singleton.mp hv] using hy
  have hshape : ({x,y} : Finset α) = highPoints F :=
    Finset.eq_of_subset_of_card_le hpair (by
      simpa only [Finset.card_pair hxy] using
        Erdos20V12HighCard.high_points_card_le_two F hu hf)
  apply two_independent_high_card_le_eighty F hu hf x y hx hy hj
  intro v hvx hvy
  have hb := Erdos20RankFour.rank_four_degree_le_twenty F hu hf v
  change degree F v ≤ 20 at hb
  have hn : degree F v ≠ 20 := by
    intro he
    have hm := degree_twenty_mem_high F v he
    rw [← hshape] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton,hvx,hvy,false_or] at hm
  omega

end FrontierTwoHighEighty
