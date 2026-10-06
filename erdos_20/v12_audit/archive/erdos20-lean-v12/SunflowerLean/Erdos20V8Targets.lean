import SunflowerLean.Erdos20RankFourWitness
import SunflowerLean.Erdos20MeetingFiftySix
import SunflowerLean.Erdos20FortyOne

namespace Erdos20V8Targets
open Erdos20RankFourWitness Erdos20IteratedLower Erdos20Substitution
open Erdos20RankThree Erdos20MeetingFiftySix

/-- Universal intersecting rank-four upper bound, over every finite family
in an arbitrary small ambient type. -/
def IntersectingRankFourUpper (N : ℕ) : Prop :=
  ∀ {α : Type} [DecidableEq α] (F : Finset (Finset α)),
    (∀ S ∈ F, S.card = 4) → IsSunflowerFree F 3 →
    (∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) → F.card ≤ N

/-- Universal unrestricted rank-four upper bound with the same sunflower convention. -/
def RankFourUpper (N : ℕ) : Prop :=
  ∀ {α : Type} [DecidableEq α] (F : Finset (Finset α)),
    (∀ S ∈ F, S.card = 4) → IsSunflowerFree F 3 → F.card ≤ N

/-- The actual twenty-seven-member construction rules out every smaller
universal intersecting upper bound. -/
theorem intersecting_upper_at_least_twenty_seven {N : ℕ}
    (h : IntersectingRankFourUpper N) : 27 ≤ N := by
  obtain ⟨α,inst,F,hu,hf,hc,hi⟩ := twenty_seven_intersecting_witness
  letI := inst
  simpa [hc] using h F hu hf hi

theorem not_intersecting_upper_below_twenty_seven {N : ℕ} (hN : N < 27) :
    ¬ IntersectingRankFourUpper N := by
  intro h
  have := intersecting_upper_at_least_twenty_seven h
  omega

theorem not_intersecting_upper_twenty_six : ¬ IntersectingRankFourUpper 26 :=
  not_intersecting_upper_below_twenty_seven (by decide)

/-- Doubling the known intersecting construction gives the unrestricted barrier54. -/
theorem unrestricted_upper_at_least_fifty_four {N : ℕ}
    (h : RankFourUpper N) : 54 ≤ N := by
  obtain ⟨α,inst,F,hu,hf,hc⟩ := fifty_four_witness
  letI := inst
  simpa [hc] using h F hu hf

theorem not_unrestricted_upper_below_fifty_four {N : ℕ} (hN : N < 54) :
    ¬ RankFourUpper N := by
  intro h
  have := unrestricted_upper_at_least_fifty_four h
  omega

/-- The literature's intersecting ceiling is an explicit premise here.
This theorem neither assumes it as an axiom nor certifies its external search. -/
theorem unrestricted_upper_of_intersecting_upper {I : ℕ}
    (hI : IntersectingRankFourUpper I) : RankFourUpper (56 + I) := by
  intro α inst F hu hf
  classical
  by_cases he : F = ∅
  · simp [he]
  obtain ⟨R,hR⟩ := Finset.nonempty_iff_ne_empty.mpr he
  let D := F.filter (fun S => S ∩ R = ∅)
  have hdu : ∀ S ∈ D, S.card = 4 := fun S hS => hu S (Finset.mem_filter.mp hS).1
  have hdf : IsSunflowerFree D 3 := by
    intro G hG hsun
    exact hf G (hG.trans (Finset.filter_subset _ _)) hsun
  have hdi : ∀ S ∈ D, ∀ T ∈ D, (S ∩ T).Nonempty := by
    intro S hS T hT
    exact disjoint_anchor_family_intersecting F R hR
      (Finset.card_pos.mp (by rw [hu R hR]; decide)) hf S hS T hT
      (Finset.card_pos.mp (by rw [hdu S hS]; decide))
      (Finset.card_pos.mp (by rw [hdu T hT]; decide))
  have hd := hI D hdu hdf hdi
  have hm := meeting_neighborhood_card_le_fifty_six F R hR hu hf
  have hp := Finset.filter_card_add_filter_neg_card_eq_card
    (s := F) (p := fun S => (S ∩ R).Nonempty)
  simp only [Finset.not_nonempty_iff_eq_empty] at hp
  change (F.filter (fun S => (S ∩ R).Nonempty)).card + D.card = F.card at hp
  clear * - hd hm hp
  omega

theorem unrestricted_upper_eighty_three_of_intersecting_twenty_seven
    (hI : IntersectingRankFourUpper 27) : RankFourUpper 83 := by
  exact unrestricted_upper_of_intersecting_upper hI

end Erdos20V8Targets
