import SunflowerLean.Erdos20V9HighIncidence

namespace Erdos20V9HighGraph
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20V8DesignCounts Erdos20V8Boundary Erdos20DegreeCongruences
open Erdos20V8HighWeights Erdos20ExtremalTwenty Erdos20V9HighIncidence

/-- High points sharing a member with a given distinct point. -/
def highNeighbors {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x : α) : Finset α :=
  support (residualLink F {x}) ∩ highPoints F

theorem mem_highNeighbors_iff {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (x y : α) :
    y ∈ highNeighbors F x ↔ y ∈ highPoints F ∧ y ≠ x ∧ ∃ R ∈ F, x ∈ R ∧ y ∈ R := by
  constructor
  · intro h
    obtain ⟨hyL,hyH⟩ := Finset.mem_inter.mp h
    obtain ⟨P,hP,hyP⟩ := Finset.mem_biUnion.mp hyL
    obtain ⟨R,hR,hxR,hRP⟩ := mem_residualLink_iff.mp hP
    rw [← hRP] at hyP
    obtain ⟨hyR,hyx⟩ := Finset.mem_sdiff.mp hyP
    exact ⟨hyH,by simpa using hyx,R,hR,Finset.singleton_subset_iff.mp hxR,hyR⟩
  · rintro ⟨hyH,hyx,R,hR,hxR,hyR⟩
    apply Finset.mem_inter.mpr
    refine ⟨Finset.mem_biUnion.mpr ⟨R \ {x},?_,?_⟩,hyH⟩
    · exact mem_residualLink_iff.mpr ⟨R,hR,Finset.singleton_subset_iff.mpr hxR,rfl⟩
    · simp [hyR,hyx]

/-- High-capacity two in the original family becomes capacity one in a high point link. -/
theorem high_link_cap_one {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hcap : ∀ R ∈ F, (R ∩ highPoints F).card ≤ 2)
    (x : α) (hx : x ∈ highPoints F) :
    ∀ P ∈ residualLink F {x}, (P ∩ highPoints F).card ≤ 1 := by
  intro P hP
  obtain ⟨R,hR,hxR,hRP⟩ := mem_residualLink_iff.mp hP
  have he := residual_inter_card R (highPoints F) x (Finset.singleton_subset_iff.mp hxR) hx
  rw [hRP] at he
  have := hcap R hR
  omega

/-- The graph on high points has maximum degree two, under the explicit local cap. -/
theorem high_point_high_neighbors_le_two {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (hcap : ∀ R ∈ F, (R ∩ highPoints F).card ≤ 2)
    (x : α) (hx : x ∈ highPoints F) : (highNeighbors F x).card ≤ 2 := by
  let L := residualLink F {x}
  have huL : ∀ P ∈ L, P.card=3 := by simpa using residualLink_uniform (core := ({x} : Finset α)) hu
  have hfL : IsSunflowerFree L 3 := residualLink_sunflowerFree hf
  have hcL : L.card=20 := by
    simpa [L,card_residualLink,upperStar,degree] using (Finset.mem_filter.mp hx).2
  exact twenty_link_distinguished_support_card_le_two L huL hfL hcL (highPoints F)
    (high_link_cap_one F hcap x hx)

/-- A point outside the high class pays at least four of its member incidences
for every high neighbor. -/
theorem four_mul_low_high_neighbors_le_degree {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (hcap : ∀ R ∈ F, (R ∩ highPoints F).card ≤ 2)
    (x : α) (hx : x ∉ highPoints F) :
    4*(highNeighbors F x).card ≤ degree F x := by
  classical
  let G := F.filter (fun R => x ∈ R)
  let K := highNeighbors F x
  have hinter (R : Finset α) (hR : R ∈ G) : R ∩ K = R ∩ highPoints F := by
    ext y
    simp only [Finset.mem_inter]
    constructor
    · intro h
      exact ⟨h.1,(mem_highNeighbors_iff F x y).mp h.2 |>.1⟩
    · intro h
      exact ⟨h.1,(mem_highNeighbors_iff F x y).mpr ⟨h.2,fun he => hx (he ▸ h.2),R,
        (Finset.mem_filter.mp hR).1,(Finset.mem_filter.mp hR).2,h.1⟩⟩
  have hdeg (y : α) (hy : y ∈ K) : (G.filter (fun R => y ∈ R)).card=5 := by
    obtain ⟨hyH,hyx,R,hR,hxR,hyR⟩ := (mem_highNeighbors_iff F x y).mp hy
    have he : G.filter (fun R => y ∈ R) = upperStar F {y,x} := by
      ext S
      simp only [G,upperStar,Finset.mem_filter,Finset.insert_subset_iff,Finset.singleton_subset_iff]
      tauto
    rw [he]
    have hp := degree_twenty_pair_codegree_zero_or_five F hu hf y x hyx (Finset.mem_filter.mp hyH).2
    have hpos : 0 < (upperStar F {y,x}).card := Finset.card_pos.mpr ⟨R,mem_upperStar_iff.mpr ⟨hR,by simp [Finset.insert_subset_iff,hxR,hyR]⟩⟩
    omega
  have hdouble (y : α) (hy : y ∈ K) :
      ((G.filter (fun R => (R ∩ K).card=2)).filter (fun R => y ∈ R)).card ≤ 2 := by
    obtain ⟨hyH,hyx,_⟩ := (mem_highNeighbors_iff F x y).mp hy
    let D := (G.filter (fun R => (R ∩ K).card=2)).filter (fun R => y ∈ R)
    have hDmem (R : Finset α) (hR : R ∈ D) : R ∈ F ∧ x ∈ R ∧ y ∈ R ∧ (R ∩ highPoints F).card=2 := by
      obtain ⟨hRGK,hyR⟩ := Finset.mem_filter.mp hR
      obtain ⟨hRG,hcard⟩ := Finset.mem_filter.mp hRGK
      rw [hinter R hRG] at hcard
      exact ⟨(Finset.mem_filter.mp hRG).1,(Finset.mem_filter.mp hRG).2,hyR,hcard⟩
    have hinj : Set.InjOn (fun R : Finset α => R \ {y}) D := by
      intro R hR S hS he
      exact sdiff_injOn_upperStar F {y}
        (mem_upperStar_iff.mpr ⟨(hDmem R hR).1,Finset.singleton_subset_iff.mpr (hDmem R hR).2.2.1⟩)
        (mem_upperStar_iff.mpr ⟨(hDmem S hS).1,Finset.singleton_subset_iff.mpr (hDmem S hS).2.2.1⟩) he
    have hsub : D.image (fun R => R \ {y}) ⊆
        (residualLink F {y}).filter (fun P => x ∈ P ∧ (P ∩ highPoints F).Nonempty) := by
      intro P hP
      obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨hRF,hxR,hyR,hcard⟩ := hDmem R hR
      have he := residual_inter_card R (highPoints F) y hyR hyH
      apply Finset.mem_filter.mpr
      refine ⟨mem_residualLink_iff.mpr ⟨R,hRF,Finset.singleton_subset_iff.mpr hyR,rfl⟩,?_,?_⟩
      · simp [hxR,Ne.symm hyx]
      · apply Finset.card_pos.mp
        omega
    let L := residualLink F {y}
    have huL : ∀ P ∈ L, P.card=3 := by simpa using residualLink_uniform (core := ({y} : Finset α)) hu
    have hfL : IsSunflowerFree L 3 := residualLink_sunflowerFree hf
    have hcL : L.card=20 := by simpa [L,card_residualLink,upperStar,degree] using (Finset.mem_filter.mp hyH).2
    calc
      D.card = (D.image (fun R => R \ {y})).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ 2 := twenty_link_point_distinguished_card_le_two L huL hfL hcL (highPoints F)
        (high_link_cap_one F hcap y hyH) x hx
  exact degree_five_distinguished_count G K (fun R hR => by rw [hinter R hR]; exact hcap R (Finset.mem_filter.mp hR).1) hdeg hdouble

/-- Every non-high point has at most four high neighbors. -/
theorem low_point_high_neighbors_le_four {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (hcap : ∀ R ∈ F, (R ∩ highPoints F).card ≤ 2)
    (x : α) (hx : x ∉ highPoints F) : (highNeighbors F x).card ≤ 4 := by
  have h4 := four_mul_low_high_neighbors_le_degree F hu hf hcap x hx
  have hb := Erdos20RankFour.rank_four_degree_le_twenty F hu hf x
  change degree F x ≤ 20 at hb
  have hne : degree F x ≠ 20 := by
    intro he
    have hpos : 0 < (F.filter (fun R => x ∈ R)).card := by change 0 < degree F x; omega
    obtain ⟨R,hR⟩ := Finset.card_pos.mp hpos
    exact hx (Finset.mem_filter.mpr ⟨member_subset_support (Finset.mem_filter.mp hR).1 (Finset.mem_filter.mp hR).2,he⟩)
  omega

/-- Each high point has at least ten supported non-high neighbors. -/
theorem high_point_low_neighbors_ge_ten {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (hcap : ∀ R ∈ F, (R ∩ highPoints F).card ≤ 2)
    (x : α) (hx : x ∈ highPoints F) :
    10 ≤ (support (residualLink F {x}) \ highPoints F).card := by
  let L := residualLink F {x}
  have huL : ∀ P ∈ L, P.card=3 := by simpa using residualLink_uniform (core := ({x} : Finset α)) hu
  have hfL : IsSunflowerFree L 3 := residualLink_sunflowerFree hf
  have hcL : L.card=20 := by simpa [L,card_residualLink,upperStar,degree] using (Finset.mem_filter.mp hx).2
  have hs := (extremal_twenty_regular_twelve L huL hfL hcL).1
  have h2 := high_point_high_neighbors_le_two F hu hf hcap x hx
  have he := Finset.card_sdiff_add_card_inter (support L) (highPoints F)
  change (support L ∩ highPoints F).card ≤ 2 at h2
  change 10 ≤ (support L \ highPoints F).card
  omega

/-- The low-neighbor/high-neighbor incidence relation is symmetric. -/
theorem high_low_incidence_identity {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) :
    (∑ x ∈ highPoints F, (support (residualLink F {x}) \ highPoints F).card) =
      ∑ y ∈ support F \ highPoints F, (highNeighbors F y).card := by
  classical
  let low := support F \ highPoints F
  let rel := fun x y => ∃ R ∈ F, x ∈ R ∧ y ∈ R
  have hleft (x : α) (hx : x ∈ highPoints F) :
      support (residualLink F {x}) \ highPoints F = low.filter (rel x) := by
    ext y
    constructor
    · intro hy
      obtain ⟨hyL,hyH⟩ := Finset.mem_sdiff.mp hy
      obtain ⟨P,hP,hyP⟩ := Finset.mem_biUnion.mp hyL
      obtain ⟨R,hR,hxR,hRP⟩ := mem_residualLink_iff.mp hP
      rw [← hRP] at hyP
      have hyR := (Finset.mem_sdiff.mp hyP).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨member_subset_support hR hyR,hyH⟩,
        R,hR,Finset.singleton_subset_iff.mp hxR,hyR⟩
    · intro hy
      obtain ⟨hyLow,R,hR,hxR,hyR⟩ := Finset.mem_filter.mp hy
      have hyx : y ≠ x := fun he => (Finset.mem_sdiff.mp hyLow).2 (he ▸ hx)
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨R \ {x},
        mem_residualLink_iff.mpr ⟨R,hR,Finset.singleton_subset_iff.mpr hxR,rfl⟩,
        by simp [hyR,hyx]⟩,(Finset.mem_sdiff.mp hyLow).2⟩
  have hright (y : α) (hy : y ∈ low) : highNeighbors F y = (highPoints F).filter (fun x => rel x y) := by
    ext x
    rw [mem_highNeighbors_iff]
    simp only [Finset.mem_filter,rel]
    constructor
    · rintro ⟨hx,_,R,hR,hyR,hxR⟩
      exact ⟨hx,R,hR,hxR,hyR⟩
    · rintro ⟨hx,R,hR,hxR,hyR⟩
      exact ⟨hx,fun he => (Finset.mem_sdiff.mp hy).2 (he ▸ hx),R,hR,hyR,hxR⟩
  calc
    _ = ∑ x ∈ highPoints F, (low.filter (rel x)).card := Finset.sum_congr rfl (fun x hx => congrArg Finset.card (hleft x hx))
    _ = ∑ y ∈ low, ((highPoints F).filter (fun x => rel x y)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun y hy => congrArg Finset.card (hright y hy).symm)

/-- Global high-low incidence capacity. Each high point needs ten low neighbors,
whereas a low point can be used by at most four high points. -/
theorem ten_mul_high_card_le_four_mul_low_card {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (hcap : ∀ R ∈ F, (R ∩ highPoints F).card ≤ 2) :
    10*(highPoints F).card ≤ 4*(support F \ highPoints F).card := by
  calc
    _ = ∑ _x ∈ highPoints F, 10 := by simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ highPoints F, (support (residualLink F {x}) \ highPoints F).card :=
      Finset.sum_le_sum (fun x hx => high_point_low_neighbors_ge_ten F hu hf hcap x hx)
    _ = ∑ y ∈ support F \ highPoints F, (highNeighbors F y).card := high_low_incidence_identity F
    _ ≤ ∑ _y ∈ support F \ highPoints F, 4 := Finset.sum_le_sum
      (fun y hy => low_point_high_neighbors_le_four F hu hf hcap y (Finset.mem_sdiff.mp hy).2)
    _ = _ := by simp [Nat.mul_comm]

end Erdos20V9HighGraph
