import SunflowerLean.Erdos20V13Intersecting
import SunflowerLean.Erdos20Incidence
import SunflowerLean.Erdos20V11CensusCapacity

namespace FrontierPairSix
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence

/-- A finite incidence deficit forces a common point in the opposite family.
The second family may be empty; the nonempty ambient set handles that case. -/
theorem common_point_of_incidence_defect
    {α : Type*} [DecidableEq α] (X D : Finset (Finset α)) (U : Finset α)
    (d : ℕ) (hU : U.Nonempty)
    (hDU : ∀ T ∈ D, T ⊆ U)
    (hcross : ∀ R ∈ X, ∀ T ∈ D, (R ∩ T).Nonempty)
    (hcap : ∀ u ∈ U, (X.filter (fun R => u ∈ R)).card ≤ d)
    (hdef : U.card*d < 2*X.card) :
    ∃ u ∈ U, ∀ T ∈ D, u ∈ T := by
  classical
  by_cases hD : D.Nonempty
  · have hsmall : ∃ R ∈ X, (R ∩ U).card ≤ 1 := by
      by_contra hn
      push_neg at hn
      have hlo : 2*X.card ≤ ∑ R ∈ X, (R ∩ U).card := by
        calc
          2*X.card = ∑ _R ∈ X, 2 := by simp [Nat.mul_comm]
          _ ≤ _ := Finset.sum_le_sum (fun R hR => by have := hn R hR; omega)
      have hhi : (∑ u ∈ U, (X.filter (fun R => u ∈ R)).card) ≤ U.card*d := by
        calc
          _ ≤ ∑ _u ∈ U, d := Finset.sum_le_sum (fun u hu => hcap u hu)
          _ = _ := by simp
      have he := incidence_sum_eq X U
      omega
    obtain ⟨R,hRX,hRsmall⟩ := hsmall
    obtain ⟨T,hTD⟩ := hD
    obtain ⟨v,hv⟩ := hcross R hRX T hTD
    have hRU : (R ∩ U).Nonempty :=
      ⟨v, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1,
        hDU T hTD (Finset.mem_inter.mp hv).2⟩⟩
    have hRcard : (R ∩ U).card = 1 := by have := hRU.card_pos; omega
    obtain ⟨u,hu⟩ := Finset.card_eq_one.mp hRcard
    have huU : u ∈ U := by
      have h : u ∈ R ∩ U := by rw [hu]; simp
      exact (Finset.mem_inter.mp h).2
    refine ⟨u,huU,?_⟩
    intro S hSD
    obtain ⟨w,hw⟩ := hcross R hRX S hSD
    have hwRU : w ∈ R ∩ U := Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hw).1,hDU S hSD (Finset.mem_inter.mp hw).2⟩
    have hwu : w = u := by simpa only [hu,Finset.mem_singleton] using hwRU
    exact hwu ▸ (Finset.mem_inter.mp hw).2
  · obtain ⟨u,hu⟩ := hU
    exact ⟨u,hu,fun T hT => (hD ⟨T,hT⟩).elim⟩

theorem thirteen_six_four_common_point
    {α : Type*} [DecidableEq α] (X D : Finset (Finset α)) (U : Finset α)
    (hX : X.card=13) (hU : U.card=6)
    (hDU : ∀ T ∈ D, T ⊆ U)
    (hcross : ∀ R ∈ X, ∀ T ∈ D, (R ∩ T).Nonempty)
    (hcap : ∀ u ∈ U, (X.filter (fun R => u ∈ R)).card ≤ 4) :
    ∃ u ∈ U, ∀ T ∈ D, u ∈ T := by
  apply common_point_of_incidence_defect X D U 4
    (Finset.card_pos.mp (by omega)) hDU hcross hcap
  omega

/-- The only four-sets avoiding a saturated core pair and meeting all six
triangle-anchor members consist of one edge from each triangle. -/
theorem avoiding_pair_shape
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x y : α)
    (A B : Finset α) (hA : A.card=3) (hB : B.card=3) (hAB : Disjoint A B)
    (hi : ∀ R ∈ F, ∀ S ∈ F, (R ∩ S).Nonempty)
    (hanchors : ∀ C ∈ A.powersetCard 2 ∪ B.powersetCard 2, {x,y} ∪ C ∈ F)
    (R : Finset α) (hR : R ∈ F) (hR4 : R.card=4) (hxR : x ∉ R) (hyR : y ∉ R) :
    ∃ P ∈ A.powersetCard 2, ∃ Q ∈ B.powersetCard 2, R=P ∪ Q := by
  have hhit (C : Finset α) (hC : C ∈ A.powersetCard 2 ∪ B.powersetCard 2) :
      (R ∩ C).Nonempty := by
    obtain ⟨u,hu⟩ := hi R hR ({x,y} ∪ C) (hanchors C hC)
    obtain ⟨huR,huC⟩ := Finset.mem_inter.mp hu
    refine ⟨u,Finset.mem_inter.mpr ⟨huR,?_⟩⟩
    rcases Finset.mem_union.mp huC with hucore | huC
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hucore
      rcases hucore with rfl | rfl
      · exact (hxR huR).elim
      · exact (hyR huR).elim
    · exact huC
  obtain ⟨P,hPA,hPR⟩ := Erdos20SharpTriples.contains_pair_of_meets_every_pair_of_triple A R hA
    (fun C hC => hhit C (Finset.mem_union_left _ hC))
  obtain ⟨Q,hQB,hQR⟩ := Erdos20SharpTriples.contains_pair_of_meets_every_pair_of_triple B R hB
    (fun C hC => hhit C (Finset.mem_union_right _ hC))
  obtain ⟨hPA',hP2⟩ := Finset.mem_powersetCard.mp hPA
  obtain ⟨hQB',hQ2⟩ := Finset.mem_powersetCard.mp hQB
  have hPQ : Disjoint P Q := hAB.mono hPA' hQB'
  have hcard : (P ∪ Q).card=4 := by rw [Finset.card_union_of_disjoint hPQ,hP2,hQ2]
  exact ⟨P,hPA,Q,hQB,(Finset.eq_of_subset_of_card_le
    (Finset.union_subset hPR hQR) (by omega)).symm⟩

/-- Deleting the six core-pair rows from a nineteen-point star leaves thirteen. -/
theorem x_only_card_thirteen
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x y : α)
    (hx : Erdos20DegreeCongruences.degree F x=19)
    (hxy : (upperStar F {x,y}).card=6) :
    (F.filter (fun R => x ∈ R ∧ y ∉ R)).card=13 := by
  classical
  have he : (F.filter (fun R => x ∈ R)).filter (fun R => y ∈ R)=upperStar F {x,y} := by
    ext R
    simp only [Finset.mem_filter,upperStar,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    tauto
  have he' : (F.filter (fun R => x ∈ R)).filter (fun R => ¬ y ∈ R)=
      F.filter (fun R => x ∈ R ∧ y ∉ R) := by
    ext R
    simp only [Finset.mem_filter]
    tauto
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := F.filter (fun R => x ∈ R)) (p := fun R => y ∈ R)
  rw [he,he',hxy] at h
  change (F.filter (fun R => x ∈ R)).card=19 at hx
  omega

/-- The two core-pair anchor rows through a gadget point consume two units
of the sharp pair-codegree budget six. -/
theorem x_only_point_capacity_four
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x y u : α)
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3) (hxu : x≠u)
    (hanchor : 2 ≤ ((upperStar F {x,y}).filter (fun R => u ∈ R)).card) :
    ((F.filter (fun R => x ∈ R ∧ y ∉ R)).filter (fun R => u ∈ R)).card≤4 := by
  classical
  have he : (upperStar F {x,u}).filter (fun R => y ∈ R)=
      (upperStar F {x,y}).filter (fun R => u ∈ R) := by
    ext R
    simp only [upperStar,Finset.mem_filter,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    tauto
  have he' : (upperStar F {x,u}).filter (fun R => ¬ y ∈ R)=
      (F.filter (fun R => x ∈ R ∧ y ∉ R)).filter (fun R => u ∈ R) := by
    ext R
    simp only [upperStar,Finset.mem_filter,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    tauto
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := upperStar F {x,u}) (p := fun R => y ∈ R)
  rw [he,he'] at h
  have hb := Erdos20V11Census.rank_four_pair_codegree_le_six F hu hf x u hxu
  omega

/-- Actual-family bridge: saturated triangle anchors and the degree-nineteen
star force a common gadget point in every row avoiding the core pair. -/
theorem pair_avoiding_common_point
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x y : α)
    (A B : Finset α) (hA : A.card=3) (hB : B.card=3) (hAB : Disjoint A B)
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (hi : ∀ R ∈ F, ∀ S ∈ F, (R ∩ S).Nonempty)
    (hx : Erdos20DegreeCongruences.degree F x=19)
    (hxy : (upperStar F {x,y}).card=6)
    (hxout : x ∉ A ∪ B)
    (hanchors : ∀ C ∈ A.powersetCard 2 ∪ B.powersetCard 2, {x,y} ∪ C ∈ F)
    (hanchor : ∀ u ∈ A ∪ B,
      2 ≤ ((upperStar F {x,y}).filter (fun R => u ∈ R)).card) :
    ∃ u ∈ A ∪ B, ∀ R ∈ F, x ∉ R → y ∉ R → u ∈ R := by
  classical
  let X := F.filter (fun R => x ∈ R ∧ y ∉ R)
  let D := F.filter (fun R => x ∉ R ∧ y ∉ R)
  have hU : (A ∪ B).card=6 := by rw [Finset.card_union_of_disjoint hAB,hA,hB]
  have hX : X.card=13 := x_only_card_thirteen F x y hx hxy
  have hDU : ∀ R ∈ D, R ⊆ A ∪ B := by
    intro R hR
    obtain ⟨hRF,hxR,hyR⟩ := Finset.mem_filter.mp hR
    obtain ⟨P,hP,Q,hQ,hshape⟩ := avoiding_pair_shape F x y A B hA hB hAB hi hanchors
      R hRF (hu R hRF) hxR hyR
    rw [hshape]
    exact Finset.union_subset_union (Finset.mem_powersetCard.mp hP).1
      (Finset.mem_powersetCard.mp hQ).1
  obtain ⟨u,huU,hcommon⟩ := thirteen_six_four_common_point X D (A ∪ B) hX hU hDU
    (fun R hR S hS => hi R (Finset.mem_filter.mp hR).1 S (Finset.mem_filter.mp hS).1)
    (fun u huU => x_only_point_capacity_four F x y u hu hf
      (fun h => hxout (h.symm ▸ huU)) (hanchor u huU))
  exact ⟨u,huU,fun R hR hxR hyR => hcommon R (Finset.mem_filter.mpr ⟨hR,hxR,hyR⟩)⟩

#print axioms common_point_of_incidence_defect
#print axioms thirteen_six_four_common_point
#print axioms avoiding_pair_shape
#print axioms x_only_card_thirteen
#print axioms x_only_point_capacity_four
#print axioms pair_avoiding_common_point

end FrontierPairSix
