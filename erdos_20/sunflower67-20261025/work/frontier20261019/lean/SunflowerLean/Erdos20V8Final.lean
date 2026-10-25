import SunflowerLean.Erdos20V8ProfileBridge
import SunflowerLean.Erdos20V8HighDegrees
import SunflowerLean.Erdos20V8HighWeights
import SunflowerLean.Erdos20V8BoundaryReduction

/-! Full family-level exclusion of the83-member all-meeting56 boundary.
The universal upper82 theorem retains the external intersecting27 premise. -/
namespace Erdos20V8Final
open Erdos20BCWConditional Erdos20DegreeCongruences Erdos20V8Boundary
open Erdos20V8ProfileBridge Erdos20V8HighDegrees Erdos20V8HighWeights
open Erdos20V8MeetingProfile Erdos20V8Targets Erdos20V8BoundaryReduction

/-- Meeting equality at every member excludes degree18 by the pair-incidence
obstruction, leaving exactly the supported degree classes19 and20. -/
theorem all_meeting_fifty_six_degrees_nineteen_or_twenty
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (hm : ∀ R ∈ F, (F.filter (fun S => (S ∩ R).Nonempty)).card = 56) :
    ∀ x ∈ support F, degree F x = 19 ∨ degree F x = 20 := by
  intro x hx
  obtain ⟨R,hR,hxR⟩ := Finset.mem_biUnion.mp hx
  have hbound := (meeting_fifty_six_member_structure F hu hf R hR (hm R hR)).1 x hxR
  have hne : degree F x ≠ 18 := by
    intro hx18
    apply no_degree_eighteen_of_high_neighbors F x hu hf ?_ hx18
    intro S hS hxS y hyS hyx
    exact (meeting_fifty_six_member_structure F hu hf S hS (hm S hS)).2.2
      x hxS hx18 y hyS hyx
  omega

/-- No83-member rank-four SF3-free family can attain meeting56 at every anchor.
This statement has no intersecting-maximum premise. -/
theorem no_eighty_three_all_meeting_fifty_six
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3) (hc : F.card = 83)
    (hm : ∀ R ∈ F, (F.filter (fun S => (S ∩ R).Nonempty)).card = 56) : False := by
  have hp := all_meeting_fifty_six_degrees_nineteen_or_twenty F hu hf hm
  have hclasses := degree_classes_of_eighty_three F hu hc hp
  have hlocal : ∀ R ∈ F, 1 ≤ (R ∩ highPoints F).card ∧
      (R ∩ highPoints F).card ≤ 3 := by
    intro R hR
    exact (meeting_fifty_six_member_structure F hu hf R hR (hm R hR)).2.1
  have hweights : ∀ x ∈ highPoints F,
      pointWeight F (highPoints F) x = 54 ∨ pointWeight F (highPoints F) x = 61 ∨
      pointWeight F (highPoints F) x = 68 ∨ pointWeight F (highPoints F) x = 72 := by
    intro x hx
    have hw := high_point_weight_four_values F hu hf hc hp (fun R hR => (hlocal R hR).2) x hx
    tauto
  have hsum : (∑ x ∈ highPoints F, pointWeight F (highPoints F) x) = 498 := by
    rw [weighted_high_point_incidence F (highPoints F) hlocal,hc]
  exact no_nine_point_weight_sum (highPoints F) (pointWeight F (highPoints F))
    hclasses.2.1 hweights hsum

/-- A formal conditional sharpening of the literature upper83 to82.
The only unclosed numerical premise is the universal intersecting upper27. -/
theorem unrestricted_upper_eighty_two_of_intersecting_twenty_seven
    (hI : IntersectingRankFourUpper 27) : RankFourUpper 82 := by
  apply unrestricted_eighty_two_of_boundary_exclusion hI
  intro α inst F hu hf hc hm
  exact no_eighty_three_all_meeting_fifty_six F hu hf hc hm

end Erdos20V8Final
