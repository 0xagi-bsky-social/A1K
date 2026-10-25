import ProfileAClosed
import TwoHighEighty

namespace FrontierFinalEighty
open Erdos20V8Targets

/-- Both actual 81-member boundary profiles are now discharged. The published
intersecting bound I(27) is retained explicitly as the sole ordinary input. -/
theorem rank_four_upper_eighty_of_intersecting_twenty_seven
    (hI : IntersectingRankFourUpper 27) : RankFourUpper 80 :=
  FrontierProfileAClosed.rank_four_upper_eighty_of_intersecting_and_no_profile_b
    hI FrontierTwoHighEighty.profile_b_not_realizable

/-- Statement-fidelity root: public aliases, including sunflower-freeness,
are expanded on both sides. Families are finite sets of distinct four-sets;
three-element sunflower subfamilies may have an empty core. Ambient types are
exactly Type, matching the inherited public universal-bound interface. -/
theorem literal_intersecting_twenty_seven_implies_eighty
    (hI : ∀ {α : Type} [DecidableEq α] (F : Finset (Finset α)),
      (∀ S ∈ F, S.card = 4) →
      (∀ H : Finset (Finset α), H ⊆ F →
        ¬(H.card = 3 ∧ ∃ core : Finset α,
          ∀ S T : Finset α, S ∈ H → T ∈ H → S ≠ T → S ∩ T = core)) →
      (∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) → F.card ≤ 27) :
    ∀ {α : Type} [DecidableEq α] (F : Finset (Finset α)),
      (∀ S ∈ F, S.card = 4) →
      (∀ H : Finset (Finset α), H ⊆ F →
        ¬(H.card = 3 ∧ ∃ core : Finset α,
          ∀ S T : Finset α, S ∈ H → T ∈ H → S ≠ T → S ∩ T = core)) →
      F.card ≤ 80 := by
  exact rank_four_upper_eighty_of_intersecting_twenty_seven hI

end FrontierFinalEighty
