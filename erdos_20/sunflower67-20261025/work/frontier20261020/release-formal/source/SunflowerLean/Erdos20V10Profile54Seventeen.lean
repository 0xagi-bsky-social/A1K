import SunflowerLean.Erdos20V10Profile54ScoreBridge

namespace Erdos20V10Profile54Seventeen
open Erdos20BCWConditional Erdos20StrictCore Erdos20RankThree Erdos20RankFour
open Erdos20V8Global Erdos20V8Boundary Erdos20DegreeCongruences Erdos20V10Profile54Bridge

/-- At the all-meeting54 boundary, a point of degree at most17 cannot
have a saturated singleton trace at any incident member. -/
theorem singleton_trace_le_nine_of_degree_le_seventeen
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card=4) (hf : IsSunflowerFree F 3)
    (hm : ∀ R ∈ F, 54 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card)
    (R : Finset α) (hR : R ∈ F) (x : α) (hx : x ∈ R)
    (hd : degree F x≤17) : (exactTrace F R {x}).card≤9 := by
  classical
  by_contra hn
  have hb := singleton_trace_card_le_ten F R {x} hR hu hf (by simp)
  have hsat : (exactTrace F R {x}).card=10 := by omega
  let L := residualLink F {x}
  let H := residualLink (exactTrace F R {x}) {x}
  have hHL : H ⊆ L := by
    intro P hP
    obtain ⟨S,hS,hxS,hSP⟩ := mem_residualLink_iff.mp hP
    exact mem_residualLink_iff.mpr ⟨S,(Finset.mem_filter.mp hS).1,hxS,hSP⟩
  have hHc : H.card=10 := by simpa [H,exact_trace_card_residual] using hsat
  have hHi : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty :=
    exact_trace_residual_intersecting F R {x} 4 hR hu hf (by simp)
  obtain ⟨A,hAH⟩ := Finset.card_pos.mp (show 0<H.card by omega)
  obtain ⟨S,hSC,hxS,hSA⟩ := mem_residualLink_iff.mp hAH
  have hSF : S ∈ F := (Finset.mem_filter.mp hSC).1
  have hxS' : x ∈ S := Finset.singleton_subset_iff.mp hxS
  have hlo := meeting_at_least_fifty_four_degree_trace_score F hu hf S hSF (hm S hSF) x hxS'
  have hsub : exactTrace L A ∅ ⊆ L \ H := by
    intro B hB
    obtain ⟨hBL,hBA⟩ := Finset.mem_filter.mp hB
    refine Finset.mem_sdiff.mpr ⟨hBL,?_⟩
    intro hBH
    have hh := hHi B hBH A hAH
    rw [hBA] at hh
    exact Finset.not_nonempty_empty hh
  have hle := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hHL,hHc] at hle
  have hLc : L.card≤17 := by simpa [L,card_residualLink,upperStar,degree] using hd
  have hEq : (exactTrace F S {x}).card = (exactTrace L A ∅).card := by
    rw [← exact_trace_card_residual F S {x}]
    have hh := singleton_residual_eq_empty_link_trace F S x hxS'
    rw [hSA] at hh
    exact congrArg Finset.card hh
  rw [hEq] at hlo
  omega

end Erdos20V10Profile54Seventeen
