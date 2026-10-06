import SunflowerLean.Erdos20V10HighParity

namespace Erdos20V10HighParity
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20V8DesignCounts Erdos20V8Boundary Erdos20DegreeCongruences
open Erdos20ExtremalTwenty Erdos20V9HighGraph Erdos20V9HighCompatibility

/-- In a member through a low point, all its high points are high neighbors. -/
theorem low_star_high_inter_eq
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (x : α) (hx : x ∉ highPoints F) (R : Finset α) (hR : R ∈ F) (hxR : x ∈ R) :
    R ∩ highNeighbors F x = R ∩ highPoints F := by
  ext y
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨hyR,hy⟩
    exact ⟨hyR,((mem_highNeighbors_iff F x y).mp hy).1⟩
  · rintro ⟨hyR,hy⟩
    exact ⟨hyR,(mem_highNeighbors_iff F x y).mpr
      ⟨hy,fun he => hx (he ▸ hy),R,hR,hxR,hyR⟩⟩

/-- A high neighbor contributes exactly five members to a low point star. -/
theorem low_high_neighbor_star_card_five
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (x y : α) (hy : y ∈ highNeighbors F x) :
    ((F.filter (fun R => x ∈ R)).filter (fun R => y ∈ R)).card = 5 := by
  obtain ⟨hyH,hyx,R,hR,hxR,hyR⟩ := (mem_highNeighbors_iff F x y).mp hy
  have he : (F.filter (fun R => x ∈ R)).filter (fun R => y ∈ R) =
      upperStar F {y,x} := by
    ext S
    simp only [upperStar,Finset.mem_filter,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    tauto
  rw [he]
  have hp := degree_twenty_pair_codegree_zero_or_five F hu hf y x hyx
    (Finset.mem_filter.mp hyH).2
  have hpos : 0 < (upperStar F {y,x}).card := Finset.card_pos.mpr
    ⟨R,mem_upperStar_iff.mpr ⟨hR,by simp [Finset.insert_subset_iff,hxR,hyR]⟩⟩
  omega

/-- The number of members through a low point containing two high neighbors
is even. Pair-incidence counting supplies the exact parity. -/
theorem low_star_double_high_count_even
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∉ highPoints F) :
    2 ∣ blockCount (F.filter (fun R => x ∈ R)) (highNeighbors F x) 2 := by
  classical
  let G := F.filter (fun R => x ∈ R)
  let K := highNeighbors F x
  have hcap : ∀ R ∈ G, (R ∩ K).card ≤ 2 := by
    intro R hR
    obtain ⟨hRF,hxR⟩ := Finset.mem_filter.mp hR
    change (R ∩ highNeighbors F x).card ≤ 2
    rw [low_star_high_inter_eq F x hx R hRF hxR]
    exact member_high_points_card_le_two F hu hf R hRF
  change 2 ∣ blockCount G K 2
  rw [← block_counts_second_moment G K hcap,pair_incidence_sum_eq]
  apply Finset.dvd_sum
  intro P hP
  obtain ⟨hPK,hP2⟩ := Finset.mem_powersetCard.mp hP
  obtain ⟨y,z,hyz,rfl⟩ := Finset.card_eq_two.mp hP2
  have hyK := hPK (show y ∈ ({y,z} : Finset α) by simp)
  have hzK := hPK (show z ∈ ({y,z} : Finset α) by simp)
  have hydata := (mem_highNeighbors_iff F x y).mp hyK
  have hzdata := (mem_highNeighbors_iff F x z).mp hzK
  have he : G.filter (fun R => ({y,z} : Finset α) ⊆ R) = upperStar F {y,x,z} := by
    ext R
    simp only [G,upperStar,Finset.mem_filter,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    tauto
  rw [he]
  rcases degree_twenty_triple_codegree_zero_or_two F hu hf y x z
      hydata.2.1 hyz hzdata.2.1.symm hydata.1 with h | h <;> simp [h]

/-- If high points cover the star at a low point, its degree differs from five
times its high-neighbor count by an even nonnegative number. -/
theorem low_high_transversal_degree_identity
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∉ highPoints F)
    (hcover : ∀ R ∈ F, x ∈ R → (R ∩ highPoints F).Nonempty) :
    ∃ e : ℕ, degree F x + 2 * e = 5 * (highNeighbors F x).card := by
  classical
  let G := F.filter (fun R => x ∈ R)
  let K := highNeighbors F x
  have hcap : ∀ R ∈ G, (R ∩ K).card ≤ 2 := by
    intro R hR
    obtain ⟨hRF,hxR⟩ := Finset.mem_filter.mp hR
    change (R ∩ highNeighbors F x).card ≤ 2
    rw [low_star_high_inter_eq F x hx R hRF hxR]
    exact member_high_points_card_le_two F hu hf R hRF
  have hzero : blockCount G K 0 = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro R hR
    obtain ⟨hRG,hcard⟩ := Finset.mem_filter.mp hR
    obtain ⟨hRF,hxR⟩ := Finset.mem_filter.mp hRG
    have hpos := Finset.card_pos.mpr (hcover R hRF hxR)
    change (R ∩ highNeighbors F x).card = 0 at hcard
    rw [low_star_high_inter_eq F x hx R hRF hxR] at hcard
    omega
  have htotal := block_counts_total G K hcap
  have hmoment : blockCount G K 1 + 2 * blockCount G K 2 = 5 * K.card := by
    rw [← block_counts_first_moment G K hcap,incidence_sum_eq]
    calc
      _ = ∑ _y ∈ K, 5 := Finset.sum_congr rfl
        (fun y hy => low_high_neighbor_star_card_five F hu hf x y hy)
      _ = _ := by simp [Nat.mul_comm]
  obtain ⟨e,he⟩ := low_star_double_high_count_even F hu hf x hx
  refine ⟨e,?_⟩
  change blockCount G K 2 = 2 * e at he
  have hcard : G.card = degree F x := rfl
  change degree F x + 2 * e = 5 * K.card
  clear * - hzero htotal hmoment he hcard
  omega

/-- A degree-seventeen low point cannot have its star covered by high points. -/
theorem low_high_transversal_degree_seventeen_impossible
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∉ highPoints F) (hd : degree F x = 17)
    (hcover : ∀ R ∈ F, x ∈ R → (R ∩ highPoints F).Nonempty) : False := by
  obtain ⟨e,he⟩ := low_high_transversal_degree_identity F hu hf x hx hcover
  have hk := low_point_high_neighbors_le_four F hu hf
    (member_high_points_card_le_two F hu hf) x hx
  clear * - he hd hk
  omega

/-- The same parity obstruction excludes degree nineteen under star coverage. -/
theorem low_high_transversal_degree_nineteen_impossible
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∉ highPoints F) (hd : degree F x = 19)
    (hcover : ∀ R ∈ F, x ∈ R → (R ∩ highPoints F).Nonempty) : False := by
  obtain ⟨e,he⟩ := low_high_transversal_degree_identity F hu hf x hx hcover
  have hk := low_point_high_neighbors_le_four F hu hf
    (member_high_points_card_le_two F hu hf) x hx
  clear * - he hd hk
  omega

end Erdos20V10HighParity
