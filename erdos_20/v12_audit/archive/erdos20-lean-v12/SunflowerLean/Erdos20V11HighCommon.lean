import SunflowerLean.Erdos20V11HighSupport

namespace Erdos20V11HighSupport
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence Erdos20RankThree
open Erdos20V8Boundary Erdos20DegreeCongruences Erdos20V9HighGraph
open Erdos20V10HighTriangle Erdos20ExtremalTwenty Erdos20V8DesignCounts

/-- A support shared by three independent high centers contains no high point:
otherwise that point would have two different high neighbors. -/
theorem common_high_support_disjoint_high {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x y z : α) (hx : x ∈ highPoints F) (hy : y ∈ highPoints F)
    (hz : z ∈ highPoints F) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hyNx : y ∉ highNeighbors F x) (hzNx : z ∉ highNeighbors F x)
    (hzNy : z ∉ highNeighbors F y) :
    Disjoint (support (residualLink F {z})) (highPoints F) := by
  obtain ⟨heX,heY⟩ := three_nonadjacent_high_supports_eq F hu hf x y z hx hy hz hxy hxz hyz hyNx hzNx hzNy
  apply Finset.disjoint_left.mpr
  intro w hwS hwH
  have hwX : w ∈ highNeighbors F x := Finset.mem_inter.mpr ⟨heX.symm ▸ hwS,hwH⟩
  have hwY : w ∈ highNeighbors F y := Finset.mem_inter.mpr ⟨heY.symm ▸ hwS,hwH⟩
  exact hxy (Finset.card_le_one.mp (high_point_high_neighbors_le_one F hu hf w hwH)
    x (high_neighbor_symm F x w hx hwX) y (high_neighbor_symm F y w hy hwY))

/-- Once an independent high triple exists, every high point has the same
actual twelve-point residual support. -/
theorem all_high_supports_eq_of_independent_triple {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x y z : α) (hx : x ∈ highPoints F) (hy : y ∈ highPoints F)
    (hz : z ∈ highPoints F) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hyNx : y ∉ highNeighbors F x) (hzNx : z ∉ highNeighbors F x)
    (hzNy : z ∉ highNeighbors F y) :
    ∀ w ∈ highPoints F, support (residualLink F {w}) = support (residualLink F {z}) := by
  obtain ⟨heX,heY⟩ := three_nonadjacent_high_supports_eq F hu hf x y z hx hy hz hxy hxz hyz hyNx hzNx hzNy
  have hd := common_high_support_disjoint_high F hu hf x y z hx hy hz hxy hxz hyz hyNx hzNx hzNy
  intro w hw
  by_cases hwx : w=x
  · simpa [hwx] using heX
  by_cases hwy : w=y
  · simpa [hwy] using heY
  have hwNx : w ∉ highNeighbors F x := by
    intro hn
    exact Finset.disjoint_left.mp hd (heX ▸ (Finset.mem_inter.mp hn).1) hw
  have hwNy : w ∉ highNeighbors F y := by
    intro hn
    exact Finset.disjoint_left.mp hd (heY ▸ (Finset.mem_inter.mp hn).1) hw
  have he := (three_nonadjacent_high_supports_eq F hu hf x y w hx hy hw hxy (Ne.symm hwx) (Ne.symm hwy) hyNx hwNx hwNy).1
  exact he.symm.trans heX

/-- A common low residual support rules out every member containing two high
points. This includes all high points, not only three selected centers. -/
theorem member_high_cap_one_of_common_support {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (S : Finset α)
    (hS : ∀ w ∈ highPoints F, support (residualLink F {w})=S)
    (hd : Disjoint S (highPoints F)) :
    ∀ R ∈ F, (R ∩ highPoints F).card ≤ 1 := by
  intro R hR
  apply Finset.card_le_one.mpr
  intro u hu v hv
  obtain ⟨huR,huH⟩ := Finset.mem_inter.mp hu
  obtain ⟨hvR,hvH⟩ := Finset.mem_inter.mp hv
  by_contra huv
  have hvN := (mem_highNeighbors_iff F u v).mpr ⟨hvH,Ne.symm huv,R,hR,huR,hvR⟩
  exact Finset.disjoint_left.mp hd (hS u huH ▸ (Finset.mem_inter.mp hvN).1) hvH

/-- If every high center has the same entirely low residual support, there
can be at most three high centers. Five incidences from each high center are
disjoint contributions to the degree of any point in the common support. -/
theorem high_card_le_three_of_common_low_support {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (S : Finset α) (hne : S.Nonempty)
    (hS : ∀ w ∈ highPoints F, support (residualLink F {w})=S)
    (hd : Disjoint S (highPoints F)) : (highPoints F).card ≤ 3 := by
  classical
  obtain ⟨u,huS⟩ := hne
  have huH : u ∉ highPoints F := fun hm => Finset.disjoint_left.mp hd huS hm
  have hcap := member_high_cap_one_of_common_support F S hS hd
  let G := F.filter (fun R => u ∈ R)
  have hdeg (w : α) (hw : w ∈ highPoints F) :
      (G.filter (fun R => w ∈ R)).card=5 := by
    have huw : u ≠ w := fun he => huH (he ▸ hw)
    have huL : u ∈ support (residualLink F {w}) := hS w hw ▸ huS
    obtain ⟨P,hP,huP⟩ := Finset.mem_biUnion.mp huL
    obtain ⟨R,hR,hwR,hRP⟩ := mem_residualLink_iff.mp hP
    have huR : u ∈ R := by rw [← hRP] at huP; exact (Finset.mem_sdiff.mp huP).1
    have he : G.filter (fun R => w ∈ R) = upperStar F {w,u} := by
      ext R
      simp only [G,upperStar,Finset.mem_filter,Finset.insert_subset_iff,Finset.singleton_subset_iff]
      tauto
    rw [he]
    have hp := degree_twenty_pair_codegree_zero_or_five F hu hf w u huw.symm (Finset.mem_filter.mp hw).2
    have hpos : 0 < (upperStar F {w,u}).card := Finset.card_pos.mpr
      ⟨R,mem_upperStar_iff.mpr ⟨hR,by simpa [Finset.insert_subset_iff] using And.intro (Finset.singleton_subset_iff.mp hwR) huR⟩⟩
    omega
  have hsum : 5*(highPoints F).card ≤ degree F u := by
    calc
      _ = ∑ w ∈ highPoints F, (G.filter (fun R => w ∈ R)).card := by
        rw [show (∑ w ∈ highPoints F, (G.filter (fun R => w ∈ R)).card) = ∑ _w ∈ highPoints F, 5 from
          Finset.sum_congr rfl (fun w hw => hdeg w hw)]
        simp [Nat.mul_comm]
      _ = ∑ R ∈ G, (R ∩ highPoints F).card := (incidence_sum_eq G (highPoints F)).symm
      _ ≤ ∑ _R ∈ G, 1 := Finset.sum_le_sum (fun R hR => hcap R (Finset.mem_filter.mp hR).1)
      _ = degree F u := by simp [G,degree]
  have hub := Erdos20RankFour.rank_four_degree_le_twenty F hu hf u
  change degree F u ≤ 20 at hub
  have hne20 : degree F u ≠ 20 := by
    intro he
    have hp : 0 < (F.filter (fun R => u ∈ R)).card := by change 0 < degree F u; omega
    obtain ⟨R,hR⟩ := Finset.card_pos.mp hp
    exact huH (Finset.mem_filter.mpr ⟨member_subset_support (Finset.mem_filter.mp hR).1
      (Finset.mem_filter.mp hR).2,he⟩)
  omega

/-- An independent high triple exhausts the entire high class. In particular,
there are exactly three high points and no high edge anywhere in the family. -/
theorem independent_high_triple_exhausts_high_class {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x y z : α) (hx : x ∈ highPoints F) (hy : y ∈ highPoints F)
    (hz : z ∈ highPoints F) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hyNx : y ∉ highNeighbors F x) (hzNx : z ∉ highNeighbors F x)
    (hzNy : z ∉ highNeighbors F y) : highPoints F = {x,y,z} := by
  have hd := common_high_support_disjoint_high F hu hf x y z hx hy hz hxy hxz hyz hyNx hzNx hzNy
  have hS := all_high_supports_eq_of_independent_triple F hu hf x y z hx hy hz hxy hxz hyz hyNx hzNx hzNy
  have hcS := (high_link_twenty_and_support_twelve F hu hf z hz).2
  have hc := high_card_le_three_of_common_low_support F hu hf _ (Finset.card_pos.mp (by omega)) hS hd
  symm
  apply Finset.eq_of_subset_of_card_le
  · simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
    exact ⟨hx,hy,hz⟩
  · have htriple : ({x,y,z} : Finset α).card=3 := by simp [hxy,hxz,hyz]
    omega

end Erdos20V11HighSupport
