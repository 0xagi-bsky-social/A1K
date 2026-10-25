import GenericHeavyExtensions

namespace FrontierCompletionMass
open Erdos20DegreeCongruences
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence

variable {α : Type*} [DecidableEq α]

/-- Any family whose members all meet a set contributes at least its cardinality
in incidence mass on that set. -/
theorem card_le_degree_sum_of_meeting
    (G W : Finset (Finset α)) (A : Finset α)
    (hGW : G ⊆ W) (hmeet : ∀ R ∈ G, (R ∩ A).Nonempty) :
    G.card ≤ ∑ a ∈ A, degree W a := by
  have hlocal : G.card ≤ ∑ R ∈ G, (R ∩ A).card := by
    calc
      G.card = ∑ _R ∈ G, 1 := by simp
      _ ≤ ∑ R ∈ G, (R ∩ A).card := Finset.sum_le_sum (fun R hR =>
        Finset.card_pos.mpr (hmeet R hR))
  have hsum : (∑ R ∈ G, (R ∩ A).card) ≤ ∑ R ∈ W, (R ∩ A).card :=
    Finset.sum_le_sum_of_subset_of_nonneg hGW (by intros; omega)
  have hi := incidence_sum_eq W A
  exact hlocal.trans (hsum.trans_eq hi)

/-- A collection with exactly one point in A carries total A-incidence equal
to its number of members. -/
theorem degree_sum_eq_card_of_singleton_intersection
    (W : Finset (Finset α)) (A : Finset α)
    (hone : ∀ R ∈ W, (R ∩ A).card = 1) :
    (∑ a ∈ A, degree W a) = W.card := by
  have hi := incidence_sum_eq W A
  have he : (∑ R ∈ W, (R ∩ A).card) = W.card := by
    calc
      _ = ∑ _R ∈ W, 1 := Finset.sum_congr rfl hone
      _ = _ := by simp
  exact hi.symm.trans he

end FrontierCompletionMass
