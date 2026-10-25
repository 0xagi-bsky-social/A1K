import ProfileAConcentrated
import ProfileABridge

namespace FrontierProfileAClosed
open Erdos20BCWConditional Erdos20StrictCore Erdos20V8Targets
open FrontierProfileACounts FrontierProfileASplit FrontierProfileAConcentrated
open FrontierTwoSideConcentration

/-- The literal residual incidence profile forced by Profile A cannot occur
under the intersecting rank-four bound twenty-seven. -/
theorem residual_profile_a_impossible
    {α : Type} [DecidableEq α] (M : ResidualProfileA α)
    (hI : IntersectingRankFourUpper 27) : False := by
  obtain ⟨D⟩ := exists_designPair M
  have hs := concentrate_from_disjoint_completion_types M hI
    (support D.left) (support D.right) D.pair_one_side
    (fun R hR hr S hS hd => (D.same_side_completion R S hR hS hd hr).1)
    (fun R hR hr S hS hd => D.swap.same_side_completion_right_card R S hR hS hd hr)
  rcases hs with h | h
  · exact concentrated_impossible D hI h
  · exact concentrated_impossible D.swap hI h

/-- New endpoint: the actual pinned 81-member single-high-point boundary
profile is excluded, with I(27) its only mathematical hypothesis. -/
theorem no_profile_a_of_intersecting_twenty_seven
    (hI : IntersectingRankFourUpper 27) :
    ¬ Erdos20V13Boundary.ProfileARealizable := by
  intro hA
  obtain ⟨α,inst,⟨M⟩⟩ := FrontierProfileABridge.residual_profile_of_profile_a hA
  letI := inst
  exact residual_profile_a_impossible M hI

/-- Profile A is discharged: only I(27) and the literal Profile B exclusion
remain as ordinary inputs to the existing bound-eightyth assembly. -/
theorem rank_four_upper_eighty_of_intersecting_and_no_profile_b
    (hI : IntersectingRankFourUpper 27)
    (hB : ¬ Erdos20V13Boundary.ProfileBRealizable) : RankFourUpper 80 :=
  Erdos20V13Boundary.unrestricted_eighty_of_three_open_inputs hI
    (no_profile_a_of_intersecting_twenty_seven hI) hB

end FrontierProfileAClosed
