import SunflowerLean.Erdos20V8Global

namespace Erdos20V10DisjointDegree
open Erdos20BCWConditional Erdos20StrictCore Erdos20RankThree

/-- In a three-sunflower-free family of nonempty sets, the two disjoint
neighborhoods at the ends of a disjoint pair cannot overlap. -/
theorem disjoint_neighborhoods_disjoint
    {α : Type*} [DecidableEq α] (G : Finset (Finset α))
    (hu : ∀ A ∈ G, A.Nonempty) (hf : IsSunflowerFree G 3)
    (A B : Finset α) (hA : A ∈ G) (hB : B ∈ G) (hAB : B ∩ A = ∅) :
    Disjoint (exactTrace G A ∅) (exactTrace G B ∅) := by
  classical
  apply Finset.disjoint_left.mpr
  intro C hCA hCB
  obtain ⟨hCG,hCB⟩ := Finset.mem_filter.mp hCB
  have hmeet := disjoint_anchor_family_intersecting G A hA (hu A hA) hf C hCA B
    (Finset.mem_filter.mpr ⟨hB,hAB⟩) (hu C hCG) (hu B hB)
  rw [hCB] at hmeet
  exact Finset.not_nonempty_empty hmeet

/-- Positive minimum disjoint-neighborhood size in a nonempty family is at
most half its cardinality. This is a direct finite-set triangle-free argument. -/
theorem twice_min_disjoint_degree_le_card
    {α : Type*} [DecidableEq α] (G : Finset (Finset α)) (m : ℕ)
    (hne : G.Nonempty) (hm : 0 < m)
    (hu : ∀ A ∈ G, A.Nonempty) (hf : IsSunflowerFree G 3)
    (hd : ∀ A ∈ G, m ≤ (exactTrace G A ∅).card) : 2*m ≤ G.card := by
  classical
  obtain ⟨A,hA⟩ := hne
  obtain ⟨B,hBA⟩ := Finset.card_pos.mp (hm.trans_le (hd A hA))
  obtain ⟨hB,hAB⟩ := Finset.mem_filter.mp hBA
  have hdis := disjoint_neighborhoods_disjoint G hu hf A B hA hB hAB
  have hsub : exactTrace G A ∅ ∪ exactTrace G B ∅ ⊆ G :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis] at hc
  have ha := hd A hA
  have hb := hd B hB
  omega

end Erdos20V10DisjointDegree
