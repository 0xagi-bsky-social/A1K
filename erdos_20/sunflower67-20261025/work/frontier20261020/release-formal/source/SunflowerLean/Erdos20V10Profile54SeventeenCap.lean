import SunflowerLean.Erdos20V10Profile54Seventeen
import SunflowerLean.Erdos20V10Profile54LowScoresBridge

namespace Erdos20V10Profile54Seventeen
open Erdos20BCWConditional Erdos20RankThree Erdos20V8Boundary Erdos20DegreeCongruences
open Erdos20V10Profile54Bridge

/-- Every near-boundary member contains at most one degree17 point.
The all-meeting hypothesis rules out saturated singleton traces at such points. -/
theorem degree_seventeen_member_card_le_one
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card=4) (hf : IsSunflowerFree F 3)
    (hm : ∀ R ∈ F, 54 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card)
    (R : Finset α) (hR : R ∈ F) :
    (R.filter (fun x => degree F x=17)).card≤1 := by
  classical
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hxR,hx17⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyR,hy17⟩ := Finset.mem_filter.mp hy
  by_contra hxy
  have hsx := singleton_trace_le_nine_of_degree_le_seventeen F hu hf hm R hR x hxR (by omega)
  have hsy := singleton_trace_le_nine_of_degree_le_seventeen F hu hf hm R hR y hyR (by omega)
  apply meeting_at_least_fifty_four_not_two_low_scores F hu hf R hR (hm R hR) x hxR y hyR hxy
  · omega
  · omega

end Erdos20V10Profile54Seventeen
