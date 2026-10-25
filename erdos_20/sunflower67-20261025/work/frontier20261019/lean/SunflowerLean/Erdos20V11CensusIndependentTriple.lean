import SunflowerLean.Erdos20V11CensusCommonSupport
import SunflowerLean.Erdos20V11HighCommon

namespace Erdos20V11Census
open Erdos20BCWConditional Erdos20DegreeCongruences Erdos20ExtremalSupport
open Erdos20V8Boundary Erdos20V9HighGraph Erdos20StrictCore Erdos20Incidence
open Erdos20V11HighSupport

/-- Common-support rigidity combined with zero-high incidence capacity excludes
an independent high triple in the minimum-degree17, cardinality81 regime. -/
theorem eighty_one_min_degree_seventeen_no_independent_high_triple
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R∈F, R.card=4) (hf : IsSunflowerFree F 3) (hc : F.card=81)
    (hs : 17≤(support F).card) (hmin : ∀ w∈support F, 17≤degree F w)
    (x y z : α) (hx : x∈highPoints F) (hy : y∈highPoints F) (hz : z∈highPoints F)
    (hxy : x≠y) (hxz : x≠z) (hyz : y≠z)
    (hyNx : y∉highNeighbors F x) (hzNx : z∉highNeighbors F x)
    (hzNy : z∉highNeighbors F y) : False := by
  have hdis := common_high_support_disjoint_high F hu hf x y z hx hy hz hxy hxz hyz hyNx hzNx hzNy
  have hS := all_high_supports_eq_of_independent_triple F hu hf x y z hx hy hz hxy hxz hyz hyNx hzNx hzNy
  have hH := independent_high_triple_exhausts_high_class F hu hf x y z hx hy hz hxy hxz hyz hyNx hzNx hzNy
  have hd : (highPoints F).card=3 := by rw [hH]; simp [hxy,hxz,hyz]
  have hcap := member_high_cap_one_of_common_support F _ hS hdis
  have hNc := (high_link_twenty_and_support_twelve F hu hf z hz).2
  apply three_high_common_twelve_support_impossible F hu hf hc hd hs hmin hcap
    (support (residualLink F {z})) (by omega)
  intro w hw
  rw [hS w hw]

/-- Under the explicit I27 hypothesis, a hypothetical81-member family contains
no three pairwise nonadjacent degree-twenty points. -/
theorem conditional_eighty_one_no_independent_high_triple
    (hI : Erdos20V8Targets.IntersectingRankFourUpper 27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R∈F, R.card=4) (hf : IsSunflowerFree F 3) (hc : F.card=81)
    (x y z : α) (hx : x∈highPoints F) (hy : y∈highPoints F) (hz : z∈highPoints F)
    (hxy : x≠y) (hxz : x≠z) (hyz : y≠z)
    (hyNx : y∉highNeighbors F x) (hzNx : z∉highNeighbors F x)
    (hzNy : z∉highNeighbors F y) : False := by
  obtain ⟨hmin,hs,_⟩ := Erdos20V10BoundaryReduction.conditional_eighty_one_min_degree_and_support hI F hu hf hc
  exact eighty_one_min_degree_seventeen_no_independent_high_triple F hu hf hc hs hmin
    x y z hx hy hz hxy hxz hyz hyNx hzNx hzNy

end Erdos20V11Census
