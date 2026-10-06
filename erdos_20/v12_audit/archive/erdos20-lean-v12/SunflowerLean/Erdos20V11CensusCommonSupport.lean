import SunflowerLean.Erdos20V11CensusCapacity

namespace Erdos20V11Census
open Erdos20BCWConditional Erdos20DegreeCongruences Erdos20ExtremalSupport
open Erdos20V8Boundary Erdos20V9HighGraph Erdos20Incidence Erdos20StrictCore

/-- An empty high-neighbor set at each high point forces every member to
contain at most one high point. -/
theorem member_high_cap_one_of_high_neighbors_empty
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hn : ∀ x∈highPoints F, highNeighbors F x=∅) :
    ∀ R∈F, (R ∩ highPoints F).card≤1 := by
  intro R hR
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  have hyN : y∈highNeighbors F x := (mem_highNeighbors_iff F x y).mpr
    ⟨(Finset.mem_inter.mp hy).2,Ne.symm hxy,R,hR,
      (Finset.mem_inter.mp hx).1,(Finset.mem_inter.mp hy).1⟩
  rw [hn x (Finset.mem_inter.mp hx).2] at hyN
  exact Finset.notMem_empty y hyN

/-- A point outside the high set and a common container of all high-link
supports has no high member in its whole star. -/
theorem star_zero_high_of_outside_common_support
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (N : Finset α)
    (hN : ∀ y∈highPoints F, support (residualLink F {y})⊆N)
    (x : α) (hxH : x∉highPoints F) (hxN : x∉N) :
    ∀ R∈F, x∈R → R ∩ highPoints F=∅ := by
  intro R hR hxR
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨hyR,hyH⟩ := Finset.mem_inter.mp hy
  have hxy : x≠y := by intro he; exact hxH (he ▸ hyH)
  have hres : R \ {y} ∈ residualLink F {y} := mem_residualLink_iff.mpr
    ⟨R,hR,by simpa using hyR,rfl⟩
  have hxres : x∈support (residualLink F {y}) := member_subset_support hres
    (Finset.mem_sdiff.mpr ⟨hxR,by simpa using hxy⟩)
  exact hxN (hN y hyH hxres)

/-- Three independent high points with one common twelve-point neighbor
container cannot occur in an81-member family of minimum degree17 on at least
seventeen points. This isolates the incidence obstruction from its geometry. -/
theorem three_high_common_twelve_support_impossible
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R∈F, R.card=4) (hf : IsSunflowerFree F 3)
    (hc : F.card=81) (hd : (highPoints F).card=3)
    (hs : 17≤(support F).card) (hmin : ∀ x∈support F, 17≤degree F x)
    (hcap : ∀ R∈F, (R ∩ highPoints F).card≤1)
    (N : Finset α) (hNc : N.card≤12)
    (hN : ∀ y∈highPoints F, support (residualLink F {y})⊆N) : False := by
  have hcard : (highPoints F ∪ N).card≤15 := by
    have hh := Finset.card_union_le (highPoints F) N
    omega
  have houtside : 1 < (support F \ (highPoints F ∪ N)).card := by
    have hh := Finset.card_sdiff_add_card_inter (support F) (highPoints F ∪ N)
    have hi := Finset.card_le_card (Finset.inter_subset_right :
      support F ∩ (highPoints F ∪ N) ⊆ highPoints F ∪ N)
    omega
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp houtside
  obtain ⟨hxS,hxout⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨hyS,hyout⟩ := Finset.mem_sdiff.mp hy
  have hxH : x∉highPoints F := fun hh => hxout (Finset.mem_union_left _ hh)
  have hyH : y∉highPoints F := fun hh => hyout (Finset.mem_union_left _ hh)
  have hxN : x∉N := fun hh => hxout (Finset.mem_union_right _ hh)
  have hyN : y∉N := fun hh => hyout (Finset.mem_union_right _ hh)
  have hpair := two_zero_high_stars_degree_sum_le F hu hf x y hxy
    (star_zero_high_of_outside_common_support F N hN x hxH hxN)
    (star_zero_high_of_outside_common_support F N hN y hyH hyN)
  have hz := zero_high_card_add_twenty_high F hcap
  have hdx := hmin x hxS
  have hdy := hmin y hyS
  omega

/-- Conditional81 specialization of the common-support obstruction. -/
theorem conditional_eighty_one_three_high_common_support_impossible
    (hI : Erdos20V8Targets.IntersectingRankFourUpper 27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R∈F, R.card=4) (hf : IsSunflowerFree F 3) (hc : F.card=81)
    (hd : (highPoints F).card=3)
    (hcap : ∀ R∈F, (R ∩ highPoints F).card≤1)
    (N : Finset α) (hNc : N.card≤12)
    (hN : ∀ y∈highPoints F, support (residualLink F {y})⊆N) : False := by
  obtain ⟨hmin,hs,_⟩ := Erdos20V10BoundaryReduction.conditional_eighty_one_min_degree_and_support hI F hu hf hc
  exact three_high_common_twelve_support_impossible F hu hf hc hd hs hmin hcap N hNc hN

end Erdos20V11Census
