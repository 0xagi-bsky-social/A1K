import SunflowerLean.Erdos20DegreeCongruences

namespace Erdos20V11EdgeCapacity
open Erdos20BCWConditional Erdos20DegreeCongruences

/-- Four reserved members leave at most two further members of a core-star
whose total capacity is six. The core need not be a pair for this counting step. -/
theorem outside_core_star_card_le_two
    {α : Type*} [DecidableEq α] (F E : Finset (Finset α)) (C : Finset α)
    (hEF : E ⊆ F) (hreserve : 4 ≤ (upperStar E C).card)
    (hcapacity : (upperStar F C).card ≤ 6) :
    (upperStar (F \ E) C).card ≤ 2 := by
  have hsub : upperStar E C ∪ upperStar (F \ E) C ⊆ upperStar F C := by
    intro R hR
    rcases Finset.mem_union.mp hR with hR | hR
    · obtain ⟨hRE,hCR⟩ := mem_upperStar_iff.mp hR
      exact mem_upperStar_iff.mpr ⟨hEF hRE,hCR⟩
    · obtain ⟨hRE,hCR⟩ := mem_upperStar_iff.mp hR
      exact mem_upperStar_iff.mpr ⟨(Finset.mem_sdiff.mp hRE).1,hCR⟩
  have hdis : Disjoint (upperStar E C) (upperStar (F \ E) C) := by
    apply Finset.disjoint_left.mpr
    intro R hRE hRD
    exact (Finset.mem_sdiff.mp (mem_upperStar_iff.mp hRD).1).2
      (mem_upperStar_iff.mp hRE).1
  have hb := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis] at hb
  omega

/-- If the outside part of a point-star is covered by at most two core-stars,
each with at most two members, it contributes at most four members. -/
theorem degree_le_inside_add_four_of_two_outside_stars
    {α : Type*} [DecidableEq α] (F E P : Finset (Finset α)) (u : α) (b : ℕ)
    (hinside : degree E u ≤ b) (hP : P.card ≤ 2)
    (hcover : ∀ R ∈ F \ E, u ∈ R → ∃ C ∈ P, C ⊆ R)
    (hcapacity : ∀ C ∈ P, (upperStar (F \ E) C).card ≤ 2) :
    degree F u ≤ b + 4 := by
  classical
  have hsub : F.filter (fun R => u ∈ R) ⊆
      E.filter (fun R => u ∈ R) ∪ P.biUnion (upperStar (F \ E)) := by
    intro R hR
    obtain ⟨hRF,huR⟩ := Finset.mem_filter.mp hR
    by_cases hRE : R ∈ E
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hRE,huR⟩)
    · obtain ⟨C,hCP,hCR⟩ := hcover R (Finset.mem_sdiff.mpr ⟨hRF,hRE⟩) huR
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨C,hCP,mem_upperStar_iff.mpr ⟨Finset.mem_sdiff.mpr ⟨hRF,hRE⟩,hCR⟩⟩)
  have hsum : (P.biUnion (upperStar (F \ E))).card ≤ 4 := by
    calc
      _ ≤ ∑ C ∈ P, (upperStar (F \ E) C).card := Finset.card_biUnion_le
      _ ≤ ∑ _C ∈ P, 2 := Finset.sum_le_sum hcapacity
      _ = P.card * 2 := by simp
      _ ≤ 4 := by omega
  have hb := Finset.card_le_card hsub
  have hu := Finset.card_union_le (E.filter (fun R => u ∈ R))
    (P.biUnion (upperStar (F \ E)))
  change (F.filter (fun R => u ∈ R)).card ≤ b + 4
  change (E.filter (fun R => u ∈ R)).card ≤ b at hinside
  omega

/-- A semantic bridge may supply at most two admissible pairs and four
reserved members for each pair. The resulting point degree is at most b+4,
where b bounds the point degree in the reserved subfamily. -/
theorem degree_le_inside_add_four_of_reserved_pairs
    {α : Type*} [DecidableEq α] (F E P : Finset (Finset α)) (u : α) (b : ℕ)
    (hEF : E ⊆ F) (hinside : degree E u ≤ b) (hP : P.card ≤ 2)
    (hcover : ∀ R ∈ F \ E, u ∈ R → ∃ C ∈ P, C ⊆ R)
    (hreserve : ∀ C ∈ P, 4 ≤ (upperStar E C).card)
    (hcapacity : ∀ C ∈ P, (upperStar F C).card ≤ 6) :
    degree F u ≤ b + 4 := by
  apply degree_le_inside_add_four_of_two_outside_stars F E P u b hinside hP hcover
  intro C hC
  exact outside_core_star_card_le_two F E C hEF (hreserve C hC) (hcapacity C hC)

/-- The coarse inside bound ten already gives a strict obstruction to
minimum supported degree seventeen. -/
theorem degree_le_fourteen_of_reserved_pairs
    {α : Type*} [DecidableEq α] (F E P : Finset (Finset α)) (u : α)
    (hEF : E ⊆ F) (hinside : degree E u ≤ 10) (hP : P.card ≤ 2)
    (hcover : ∀ R ∈ F \ E, u ∈ R → ∃ C ∈ P, C ⊆ R)
    (hreserve : ∀ C ∈ P, 4 ≤ (upperStar E C).card)
    (hcapacity : ∀ C ∈ P, (upperStar F C).card ≤ 6) :
    degree F u ≤ 14 := by
  exact degree_le_inside_add_four_of_reserved_pairs F E P u 10
    hEF hinside hP hcover hreserve hcapacity

/-- The sharper inside bound eight gives degree at most twelve. -/
theorem degree_le_twelve_of_reserved_pairs
    {α : Type*} [DecidableEq α] (F E P : Finset (Finset α)) (u : α)
    (hEF : E ⊆ F) (hinside : degree E u ≤ 8) (hP : P.card ≤ 2)
    (hcover : ∀ R ∈ F \ E, u ∈ R → ∃ C ∈ P, C ⊆ R)
    (hreserve : ∀ C ∈ P, 4 ≤ (upperStar E C).card)
    (hcapacity : ∀ C ∈ P, (upperStar F C).card ≤ 6) :
    degree F u ≤ 12 := by
  exact degree_le_inside_add_four_of_reserved_pairs F E P u 8
    hEF hinside hP hcover hreserve hcapacity

end Erdos20V11EdgeCapacity
