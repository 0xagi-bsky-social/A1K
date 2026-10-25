import SunflowerLean.Erdos20V11Census
import SunflowerLean.Erdos20V10HighParityMain

namespace Erdos20V11Census
open Erdos20BCWConditional Erdos20DegreeCongruences Erdos20ExtremalSupport
open Erdos20V9Census Erdos20V8Boundary Erdos20V8DesignCounts Erdos20Incidence
open Erdos20StrictCore Erdos20V9HighGraph Erdos20V10HighParity

/-- Members avoiding every degree-twenty point. -/
def zeroHighFamily {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Finset (Finset α) :=
  F.filter (fun R => R ∩ highPoints F = ∅)

/-- Pair codegree never exceeds the sharp rank-two ceiling six. -/
theorem rank_four_pair_codegree_le_six
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x y : α) (hxy : x≠y) : (upperStar F {x,y}).card≤6 := by
  have hp : ({x,y} : Finset α).card=2 := by simp [hxy]
  have huL : ∀ P ∈ residualLink F {x,y}, P.card=2 := by
    simpa [hp] using residualLink_uniform (core := ({x,y} : Finset α)) hu
  have hh := rank_two_three_petals_card_le_six (residualLink F {x,y}) huL
    (residualLink_sunflowerFree hf)
  simpa [card_residualLink] using hh

/-- Two distinct points whose entire stars avoid high points consume at most
the zero-high family plus six repeated incidences. No geometry is assumed. -/
theorem two_zero_high_stars_degree_sum_le
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x y : α) (hxy : x≠y)
    (hx : ∀ R ∈ F, x∈R → R ∩ highPoints F = ∅)
    (hy : ∀ R ∈ F, y∈R → R ∩ highPoints F = ∅) :
    degree F x + degree F y ≤ (zeroHighFamily F).card+6 := by
  let A := F.filter (fun R => x∈R)
  let B := F.filter (fun R => y∈R)
  have hsub : A ∪ B ⊆ zeroHighFamily F := by
    intro R hR
    rcases Finset.mem_union.mp hR with hR | hR
    · obtain ⟨hRF,hxR⟩ := Finset.mem_filter.mp hR
      exact Finset.mem_filter.mpr ⟨hRF,hx R hRF hxR⟩
    · obtain ⟨hRF,hyR⟩ := Finset.mem_filter.mp hR
      exact Finset.mem_filter.mpr ⟨hRF,hy R hRF hyR⟩
  have he : A ∩ B = upperStar F {x,y} := by
    ext R
    simp only [A,B,upperStar,Finset.mem_inter,Finset.mem_filter,
      Finset.insert_subset_iff,Finset.singleton_subset_iff]
    tauto
  have hcard := Finset.card_union_add_card_inter A B
  rw [he] at hcard
  have hbound := Finset.card_le_card hsub
  have hpair := rank_four_pair_codegree_le_six F hu hf x y hxy
  change A.card+B.card ≤ (zeroHighFamily F).card+6
  omega

/-- Absence from every high point-link support forces the whole star to avoid
high points. The point must itself be low. -/
theorem star_zero_high_of_no_high_neighbors
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (x : α) (hx : x∉highPoints F) (hn : highNeighbors F x=∅) :
    ∀ R ∈ F, x∈R → R ∩ highPoints F=∅ := by
  intro R hR hxR
  rw [← low_star_high_inter_eq F x hx R hR hxR,hn,Finset.inter_empty]

/-- For an independent high set each high point accounts for twenty distinct
members, with no overlap between high stars. -/
theorem zero_high_card_add_twenty_high
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hcap : ∀ R ∈ F, (R ∩ highPoints F).card≤1) :
    (zeroHighFamily F).card + 20*(highPoints F).card = F.card := by
  have hcap2 : ∀ R ∈ F, (R ∩ highPoints F).card≤2 := fun R hR => (hcap R hR).trans (by decide)
  have ht := block_counts_total F (highPoints F) hcap2
  have hm := block_counts_first_moment F (highPoints F) hcap2
  rw [incidence_sum_eq] at hm
  have hd := degreeClass_sum F 20
  change (∑ x ∈ highPoints F, (F.filter (fun R => x∈R)).card) = 20*(highPoints F).card at hd
  rw [hd] at hm
  have hz : blockCount F (highPoints F) 0 = (zeroHighFamily F).card := by
    simp only [blockCount,zeroHighFamily,Finset.card_eq_zero]
  have htwo : blockCount F (highPoints F) 2 = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro R hR
    obtain ⟨hRF,hc⟩ := Finset.mem_filter.mp hR
    have := hcap R hRF
    omega
  omega

/-- Degree17 and degree19 points each belong to a member avoiding all high
points, by the covered-star parity obstruction. -/
theorem odd_low_degree_mem_zero_high_support
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x : α) (hd : degree F x=17 ∨ degree F x=19) : x∈support (zeroHighFamily F) := by
  classical
  have hx : x∉highPoints F := by
    intro hh
    have := (Finset.mem_filter.mp hh).2
    omega
  by_contra hn
  have hcover : ∀ R ∈ F, x∈R → (R ∩ highPoints F).Nonempty := by
    intro R hR hxR
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    apply hn
    exact member_subset_support (Finset.mem_filter.mpr ⟨hR,he⟩) hxR
  rcases hd with hd | hd
  · exact low_high_transversal_degree_seventeen_impossible F hu hf x hx hd hcover
  · exact low_high_transversal_degree_nineteen_impossible F hu hf x hx hd hcover

/-- The zero-high family must have enough point capacity to contain both odd
low-degree classes. -/
theorem odd_degree_classes_le_four_zero_high_card
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3) :
    (degreeClass F 17).card + (degreeClass F 19).card ≤ 4*(zeroHighFamily F).card := by
  have hdis : Disjoint (degreeClass F 17) (degreeClass F 19) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have := (Finset.mem_filter.mp hx).2
    have := (Finset.mem_filter.mp hy).2
    omega
  have hsub : degreeClass F 17 ∪ degreeClass F 19 ⊆ support (zeroHighFamily F) := by
    intro x hx
    apply odd_low_degree_mem_zero_high_support F hu hf x
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Or.inl (Finset.mem_filter.mp hx).2
    · exact Or.inr (Finset.mem_filter.mp hx).2
  have hs : (support (zeroHighFamily F)).card ≤ 4*(zeroHighFamily F).card := by
    calc
      _ ≤ ∑ R ∈ zeroHighFamily F, R.card := Finset.card_biUnion_le
      _ = ∑ _R ∈ zeroHighFamily F, 4 := Finset.sum_congr rfl
        (fun R hR => hu R (Finset.mem_filter.mp hR).1)
      _ = _ := by simp [Nat.mul_comm]
  rw [← Finset.card_union_of_disjoint hdis]
  exact (Finset.card_le_card hsub).trans hs

/-- Four independent high points cannot occur in a conditional81 family:
only one zero-high member would have to contain at least ten degree19 points. -/
theorem conditional_eighty_one_four_independent_high_impossible
    (hI : Erdos20V8Targets.IntersectingRankFourUpper 27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3) (hc : F.card=81)
    (hd : (highPoints F).card=4)
    (hcap : ∀ R ∈ F, (R ∩ highPoints F).card≤1) : False := by
  obtain ⟨hs,ha,ht,he,hp⟩ := conditional_eighty_one_census hI F hu hf hc
  have hz := zero_high_card_add_twenty_high F hcap
  have ho := odd_degree_classes_le_four_zero_high_card F hu hf
  clear * - hs ha ht he hp hz ho hd hc
  omega

end Erdos20V11Census
