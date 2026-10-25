import SunflowerLean.Erdos20V12HighCardGraph
import SunflowerLean.Erdos20V12HighCardPairs
import SunflowerLean.Erdos20V10HighParity

namespace Erdos20V12HighCard
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20V8Boundary Erdos20DegreeCongruences Erdos20V9HighGraph
open Erdos20V11HighSupport Erdos20V10HighParity

/-- Two low points occurring together in a high center's residual link make
that center a degree-two vertex of the actual residual pair link. -/
theorem high_center_pair_link_degree_two {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (w : α) (hw : w ∈ highPoints F) (u v : α)
    (huH : u ∉ highPoints F) (hvH : v ∉ highPoints F) (huv : u≠v)
    (hpair : ∃ P ∈ residualLink F {w}, u∈P ∧ v∈P) :
    ((residualLink F {u,v}).filter (fun P => w∈P)).card=2 := by
  have hwu : w≠u := fun he => huH (he ▸ hw)
  have hwv : w≠v := fun he => hvH (he ▸ hw)
  have hc := degree_twenty_triple_codegree_zero_or_two F hu hf w u v hwu hwv huv hw
  obtain ⟨P,hP,huP,hvP⟩ := hpair
  have hR : insert w P ∈ F := by simpa using core_union_residual_mem_family hP
  have hpos : 0<(upperStar F {w,u,v}).card := Finset.card_pos.mpr
    ⟨insert w P,mem_upperStar_iff.mpr ⟨hR,by simp [Finset.insert_subset_iff,huP,hvP]⟩⟩
  have hc2 : (upperStar F {w,u,v}).card=2 := by omega
  have hd : Disjoint ({u,v} : Finset α) {w} := by simp [hwu,hwv]
  have he := card_filter_residualLink F ({u,v} : Finset α) {w} hd
  simp only [Finset.singleton_subset_iff] at he
  have hcore : ({u,v} : Finset α) ∪ {w}={w,u,v} := by
    ext t
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  rw [hcore] at he
  exact he.trans hc2

/-- Three high centers are impossible: their common twelve-point support has
only eight component signatures, yielding a pair whose residual graph would
have three independent vertices of degree two. -/
theorem no_three_high_points {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x y z : α) (hx : x ∈ highPoints F) (hy : y ∈ highPoints F)
    (hz : z ∈ highPoints F) (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) : False := by
  obtain ⟨hyNx,hzNx,hzNy⟩ := three_high_pairwise_nonadjacent F hu hf x y z hx hy hz hxy hxz hyz
  obtain ⟨heX,heY⟩ := three_nonadjacent_high_supports_eq F hu hf x y z hx hy hz hxy hxz hyz hyNx hzNx hzNy
  have hdis := common_high_support_disjoint_high F hu hf x y z hx hy hz hxy hxz hyz hyNx hzNx hzNy
  have hsupports := all_high_supports_eq_of_independent_triple F hu hf x y z hx hy hz hxy hxz hyz hyNx hzNx hzNy
  have hhigh := independent_high_triple_exhausts_high_class F hu hf x y z hx hy hz hxy hxz hyz hyNx hzNx hzNy
  have hcap := member_high_cap_one_of_common_support F _ hsupports hdis
  have hH3 : (highPoints F).card=3 := by rw [hhigh]; simp [hxy,hxz,hyz]
  have hxu : ∀ P ∈ residualLink F {x}, P.card=3 := by
    simpa using residualLink_uniform (core := ({x} : Finset α)) hu
  have hyu : ∀ P ∈ residualLink F {y}, P.card=3 := by
    simpa using residualLink_uniform (core := ({y} : Finset α)) hu
  have hzu : ∀ P ∈ residualLink F {z}, P.card=3 := by
    simpa using residualLink_uniform (core := ({z} : Finset α)) hu
  obtain ⟨u,huS,v,hvS,huv,hpairX,hpairY,hpairZ⟩ := three_twenty_links_shared_pair
    (residualLink F {x}) (residualLink F {y}) (residualLink F {z})
    hxu (residualLink_sunflowerFree hf) (high_link_twenty_and_support_twelve F hu hf x hx).1
    hyu (residualLink_sunflowerFree hf) (high_link_twenty_and_support_twelve F hu hf y hy).1
    hzu (residualLink_sunflowerFree hf) (high_link_twenty_and_support_twelve F hu hf z hz).1 heX heY
  have huH : u ∉ highPoints F := fun h => Finset.disjoint_left.mp hdis huS h
  have hvH : v ∉ highPoints F := fun h => Finset.disjoint_left.mp hdis hvS h
  let K := residualLink F {u,v}
  have hku : ∀ P ∈ K, P.card=2 := by
    have hp : ({u,v} : Finset α).card=2 := by simp [huv]
    simpa [K,hp] using residualLink_uniform (core := ({u,v} : Finset α)) hu
  have hkcap : ∀ P ∈ K, (P ∩ highPoints F).card≤1 := by
    intro P hP
    obtain ⟨R,hR,huvR,hRP⟩ := mem_residualLink_iff.mp hP
    apply (Finset.card_le_card (show P ∩ highPoints F ⊆ R ∩ highPoints F from ?_)).trans (hcap R hR)
    intro w hw
    obtain ⟨hwP,hwH⟩ := Finset.mem_inter.mp hw
    rw [← hRP] at hwP
    exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hwP).1,hwH⟩
  have hkd : ∀ w ∈ highPoints F, (K.filter (fun P => w∈P)).card=2 := by
    intro w hw
    rw [hhigh] at hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with hw | hw | hw
    · simpa only [hw] using high_center_pair_link_degree_two F hu hf x hx u v huH hvH huv hpairX
    · simpa only [hw] using high_center_pair_link_degree_two F hu hf y hy u v huH hvH huv hpairY
    · simpa only [hw] using high_center_pair_link_degree_two F hu hf z hz u v huH hvH huv hpairZ
  exact three_independent_degree_two_impossible K hku (residualLink_sunflowerFree hf)
    (highPoints F) hH3 hkcap hkd

/-- Unconditional global ceiling: every rank-four three-sunflower-free family
has at most two degree-twenty points. No I27 or support restriction is assumed. -/
theorem high_points_card_le_two {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3) :
    (highPoints F).card≤2 := by
  by_contra hn
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ := Finset.two_lt_card_iff.mp
    (show 2<(highPoints F).card by omega)
  exact no_three_high_points F hu hf x y z hx hy hz hxy hxz hyz

end Erdos20V12HighCard
