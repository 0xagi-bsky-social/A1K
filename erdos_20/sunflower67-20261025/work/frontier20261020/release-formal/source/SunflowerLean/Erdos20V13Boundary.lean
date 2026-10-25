import SunflowerLean.Erdos20V12Final

namespace Erdos20V13Boundary
open Erdos20BCWConditional Erdos20DegreeCongruences Erdos20V8Targets
open Erdos20V9Census Erdos20V8Boundary Erdos20V12Profile

/-- The minimal numerical census yields precisely the two necessary rows.
The positive degree-19-or-20 class is essential to exclude support eighteen. -/
theorem direct_two_census_profiles (b c d : ℕ)
    (ht : 18*b+19*c+20*d=324) (hd : d≤2) (hp : 1≤c+d) :
    b+c+d=17 ∧ TwoCensusProfiles b c d := by
  unfold TwoCensusProfiles
  omega

/-- Without the positive high-degree witness the all-eighteen row survives. -/
theorem direct_census_without_positive_witness (b c d : ℕ)
    (ht : 18*b+19*c+20*d=324) (hd : d≤2) :
    TwoCensusProfiles b c d ∨ (b=18 ∧ c=0 ∧ d=0) := by
  unfold TwoCensusProfiles
  omega

/-- Actual-family bridge to the direct arithmetic proof, independent of the
legacy enumeration of ten census rows. The support-eighteen exclusion occurs
inside conditional_eighty_one_census through its positive-degree witness. -/
theorem conditional_eighty_one_two_profiles_direct
    (hI : IntersectingRankFourUpper 27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3) (hc : F.card=81) :
    (support F).card=17 ∧ degreeClass F 17=∅ ∧
    TwoCensusProfiles (degreeClass F 18).card (degreeClass F 19).card (highPoints F).card := by
  have he := conditional_eighty_one_degree_class_seventeen_empty hI F hu hf hc
  obtain ⟨hs,_,ht,_,hp⟩ := Erdos20V11Census.conditional_eighty_one_census hI F hu hf hc
  have hd := Erdos20V12HighCard.high_points_card_le_two F hu hf
  rw [he,Finset.card_empty] at hs ht
  obtain ⟨hs17,hprof⟩ := direct_two_census_profiles _ _ _ (by simpa using ht) hd hp
  have hdeg : ∀ x ∈ support F, 17 ≤ degree F x ∧ degree F x ≤ 20 := by
    intro x hx
    exact ⟨(Erdos20V10BoundaryReduction.conditional_eighty_one_min_degree_and_support hI F hu hf hc).1 x hx,
      Erdos20RankFour.rank_four_degree_le_twenty F hu hf x⟩
  have hsum := (Erdos20V11Census.four_degree_census_identity F hu hdeg).2
  rw [he,Finset.card_empty] at hsum
  exact ⟨by omega,he,hprof⟩

/-- Literal realizability obligation A. It includes all retained boundary
premises and asserts existence, not an upper bound or an axiom. -/
def ProfileARealizable : Prop :=
  ∃ (α : Type) (_ : DecidableEq α) (F : Finset (Finset α)),
    (∀ R ∈ F, R.card=4) ∧ IsSunflowerFree F 3 ∧ F.card=81 ∧
    (support F).card=17 ∧ degreeClass F 17=∅ ∧
    (degreeClass F 18).card=0 ∧ (degreeClass F 19).card=16 ∧ (highPoints F).card=1 ∧
    (∀ R ∈ F, (R ∩ highPoints F).card≤1)

/-- Literal realizability obligation B, separate from A and I27. -/
def ProfileBRealizable : Prop :=
  ∃ (α : Type) (_ : DecidableEq α) (F : Finset (Finset α)),
    (∀ R ∈ F, R.card=4) ∧ IsSunflowerFree F 3 ∧ F.card=81 ∧
    (support F).card=17 ∧ degreeClass F 17=∅ ∧
    (degreeClass F 18).card=1 ∧ (degreeClass F 19).card=14 ∧ (highPoints F).card=2 ∧
    (∀ R ∈ F, (R ∩ highPoints F).card≤1)

/-- A short terminal reduction with three explicitly open ordinary inputs. -/
theorem unrestricted_eighty_of_three_open_inputs
    (hI : IntersectingRankFourUpper 27)
    (hA : ¬ ProfileARealizable) (hB : ¬ ProfileBRealizable) : RankFourUpper 80 := by
  intro α inst F hu hf
  have h81 := Erdos20V9Final.unrestricted_upper_eighty_one_of_intersecting_twenty_seven hI F hu hf
  by_contra hn
  have hc : F.card=81 := by omega
  obtain ⟨hs,h17,hp⟩ := conditional_eighty_one_two_profiles_direct hI F hu hf hc
  have hcap := (Erdos20V11Final.conditional_eighty_one_boundary_rigidity hI F hu hf hc).2.2.2
  rcases hp with ⟨hb,hc19,hd⟩ | ⟨hb,hc19,hd⟩
  · exact hA ⟨α,inst,F,hu,hf,hc,hs,h17,hb,hc19,hd,hcap⟩
  · exact hB ⟨α,inst,F,hu,hf,hc,hs,h17,hb,hc19,hd,hcap⟩

/-- Arithmetic overlap classification; actual high-link realizability is a
separate geometric obligation. -/
theorem overlap_four_rows (n0 n1 n2 : ℕ)
    (ht : n0+n1+n2=15) (hi : n1+2*n2=24) :
    (n0=0 ∧ n1=6 ∧ n2=9) ∨ (n0=1 ∧ n1=4 ∧ n2=10) ∨
    (n0=2 ∧ n1=2 ∧ n2=11) ∨ (n0=3 ∧ n1=0 ∧ n2=12) := by omega

/-- Natural-subtraction ledger for the two deleted disjoint degree-20 stars.
This is numerical bookkeeping and does not assert existence of a Profile B family. -/
theorem residual_degree_rows (d k : ℕ) (hd : d=18 ∨ d=19) (hk : k≤2) :
    (d=18 ∧ ((k=0 ∧ d-5*k=18) ∨ (k=1 ∧ d-5*k=13) ∨ (k=2 ∧ d-5*k=8))) ∨
    (d=19 ∧ ((k=0 ∧ d-5*k=19) ∨ (k=1 ∧ d-5*k=14) ∨ (k=2 ∧ d-5*k=9))) := by omega


/-- Two size-twelve subsets of a size-fifteen universe have exactly four
possible adjacency censuses. This is a finite-set result, not a realization claim. -/
theorem two_twelve_subsets_four_rows
    {α : Type*} [DecidableEq α] (U A B : Finset α)
    (hU : U.card=15) (hA : A.card=12) (hB : B.card=12)
    (hAU : A⊆U) (hBU : B⊆U) :
    let n0 := (U \ (A ∪ B)).card
    let n1 := (A \ B).card + (B \ A).card
    let n2 := (A ∩ B).card
    (n0=0 ∧ n1=6 ∧ n2=9) ∨ (n0=1 ∧ n1=4 ∧ n2=10) ∨
    (n0=2 ∧ n1=2 ∧ n2=11) ∨ (n0=3 ∧ n1=0 ∧ n2=12) := by
  dsimp only
  apply overlap_four_rows
  all_goals
    have ha := Finset.card_sdiff_add_card_inter A B
    have hb := Finset.card_sdiff_add_card_inter B A
    rw [Finset.inter_comm B A] at hb
    have hu := Finset.card_union_add_card_inter A B
    have hrest := Finset.card_sdiff_add_card_inter U (A ∪ B)
    have habU : A ∪ B ⊆ U := Finset.union_subset hAU hBU
    rw [Finset.inter_eq_right.mpr habU] at hrest
    omega

/-- A high link has no supported high point when every member has at most one. -/
theorem high_link_support_subset_low
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hcap : ∀ R ∈ F, (R ∩ highPoints F).card≤1)
    (x : α) (hx : x∈highPoints F) :
    support (residualLink F {x}) ⊆ support F \ highPoints F := by
  intro y hy
  obtain ⟨P,hP,hyP⟩ := Finset.mem_biUnion.mp hy
  obtain ⟨R,hR,hxR,hRP⟩ := mem_residualLink_iff.mp hP
  rw [← hRP] at hyP
  obtain ⟨hyR,hyx⟩ := Finset.mem_sdiff.mp hyP
  have hxR' := Finset.singleton_subset_iff.mp hxR
  refine Finset.mem_sdiff.mpr ⟨member_subset_support hR hyR,?_⟩
  intro hyH
  have he : y=x := Finset.card_le_one.mp (hcap R hR) y
    (Finset.mem_inter.mpr ⟨hyR,hyH⟩) x (Finset.mem_inter.mpr ⟨hxR',hx⟩)
  exact hyx (by simp [he])

/-- Actual-family bridge for the Profile B high-link overlap census. The two
high centers are distinct; all counts refer to their actual residual supports. -/
theorem profile_b_actual_overlap_four_rows
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (hs : (support F).card=17) (hd : (highPoints F).card=2)
    (hcap : ∀ R ∈ F, (R ∩ highPoints F).card≤1)
    (x y : α) (hx : x∈highPoints F) (hy : y∈highPoints F) (_hxy : x≠y) :
    let U := support F \ highPoints F
    let A := support (residualLink F {x})
    let B := support (residualLink F {y})
    let n0 := (U \ (A ∪ B)).card
    let n1 := (A \ B).card + (B \ A).card
    let n2 := (A ∩ B).card
    (n0=0 ∧ n1=6 ∧ n2=9) ∨ (n0=1 ∧ n1=4 ∧ n2=10) ∨
    (n0=2 ∧ n1=2 ∧ n2=11) ∨ (n0=3 ∧ n1=0 ∧ n2=12) := by
  apply two_twelve_subsets_four_rows
  · have h := Finset.card_sdiff_add_card_inter (support F) (highPoints F)
    have hsub : highPoints F ⊆ support F := Finset.filter_subset _ _
    rw [Finset.inter_eq_right.mpr hsub] at h
    omega
  · exact (Erdos20V11HighSupport.high_link_twenty_and_support_twelve F hu hf x hx).2
  · exact (Erdos20V11HighSupport.high_link_twenty_and_support_twelve F hu hf y hy).2
  · exact high_link_support_subset_low F hcap x hx
  · exact high_link_support_subset_low F hcap y hy

/-- Actual member counts after all high stars are removed, for either profile. -/
theorem profile_zero_high_member_count
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hc : F.card=81) (hcap : ∀ R ∈ F, (R ∩ highPoints F).card≤1) :
    ((highPoints F).card=1 → (Erdos20V11Census.zeroHighFamily F).card=61) ∧
    ((highPoints F).card=2 → (Erdos20V11Census.zeroHighFamily F).card=41) := by
  have h := Erdos20V11Census.zero_high_card_add_twenty_high F hcap
  constructor <;> intro hd <;> omega


/-- Deleting all disjoint high stars removes exactly five incidences for each
high neighbor of a low point. This is an actual-family identity. -/
theorem zero_high_degree_add_five_neighbors
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (hcap : ∀ R ∈ F, (R ∩ highPoints F).card≤1)
    (x : α) (hx : x∉highPoints F) :
    degree (Erdos20V11Census.zeroHighFamily F) x +
      5*(Erdos20V9HighGraph.highNeighbors F x).card = degree F x := by
  classical
  let G := F.filter (fun R => x∈R)
  let K := Erdos20V9HighGraph.highNeighbors F x
  have hinter (R) (hR : R∈G) : R ∩ K = R ∩ highPoints F :=
    Erdos20V10HighParity.low_star_high_inter_eq F x hx R
      (Finset.mem_filter.mp hR).1 (Finset.mem_filter.mp hR).2
  have hcapG : ∀ R∈G, (R ∩ K).card≤1 := by
    intro R hR
    rw [hinter R hR]
    exact hcap R (Finset.mem_filter.mp hR).1
  have hc2 : ∀ R∈G, (R ∩ K).card≤2 := fun R hR => (hcapG R hR).trans (by decide)
  have ht := Erdos20V8DesignCounts.block_counts_total G K hc2
  have hm := Erdos20V8DesignCounts.block_counts_first_moment G K hc2
  rw [Erdos20Incidence.incidence_sum_eq] at hm
  have hs : (∑ y∈K, (G.filter (fun R => y∈R)).card)=5*K.card := by
    calc
      _ = ∑ _y∈K, 5 := Finset.sum_congr rfl (fun y hy =>
        Erdos20V10HighParity.low_high_neighbor_star_card_five F hu hf x y hy)
      _ = _ := by simp [Nat.mul_comm]
  rw [hs] at hm
  have hz : Erdos20V8DesignCounts.blockCount G K 0 =
      degree (Erdos20V11Census.zeroHighFamily F) x := by
    unfold Erdos20V8DesignCounts.blockCount degree
    congr 1
    ext R
    simp only [Finset.mem_filter,Erdos20V11Census.zeroHighFamily]
    constructor
    · rintro ⟨hRG,hcard⟩
      rw [hinter R hRG] at hcard
      exact ⟨⟨(Finset.mem_filter.mp hRG).1,Finset.card_eq_zero.mp hcard⟩,
        (Finset.mem_filter.mp hRG).2⟩
    · rintro ⟨⟨hRF,he⟩,hxR⟩
      have hRG : R∈G := Finset.mem_filter.mpr ⟨hRF,hxR⟩
      exact ⟨hRG,by rw [hinter R hRG,he]; rfl⟩
  have htwo : Erdos20V8DesignCounts.blockCount G K 2=0 := by
    unfold Erdos20V8DesignCounts.blockCount
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro R hR
    obtain ⟨hRG,hcard⟩ := Finset.mem_filter.mp hR
    have := hcapG R hRG
    omega
  change degree (Erdos20V11Census.zeroHighFamily F) x + 5*K.card = G.card
  omega

/-- Subtraction form of the preceding actual-family identity. -/
theorem zero_high_degree_eq_sub_five_neighbors
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (hcap : ∀ R ∈ F, (R ∩ highPoints F).card≤1)
    (x : α) (hx : x∉highPoints F) :
    degree (Erdos20V11Census.zeroHighFamily F) x =
      degree F x - 5*(Erdos20V9HighGraph.highNeighbors F x).card := by
  have h := zero_high_degree_add_five_neighbors F hu hf hcap x hx
  omega

end Erdos20V13Boundary


