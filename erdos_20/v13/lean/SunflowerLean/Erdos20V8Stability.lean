import SunflowerLean.Erdos20ExtremalTransversals
import SunflowerLean.Erdos20DesignNormalForm
import SunflowerLean.Erdos20ThreeCrossEdges

/-! Stability and exact transversal structure of extremal triple designs.
The extension hypotheses in the deletion results are explicit; no classification
of arbitrary nineteen-member families is assumed. -/
namespace Erdos20V8Stability
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20V5Frontier Erdos20ExtremalTransversals Erdos20ExtremalTwenty
open Erdos20RankThree Erdos20RankFour Erdos20ThreeCrossEdges

/-- An intersecting family of ten triples on six supported points chooses
exactly one member from each complementary pair of triples. -/
theorem intersecting_six_ten_complement_partition
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (hc : F.card = 10) (hs : (support F).card = 6) :
    F ∪ F.image (fun S => support F \ S) = (support F).powersetCard 3 := by
  classical
  let D := F.image (fun S => support F \ S)
  have hDc : D.card = 10 := by
    rw [Finset.card_image_of_injOn, hc]
    intro A hA B hB he
    have he' := congrArg (fun C => support F \ C) he
    simpa only [Finset.sdiff_sdiff_eq_self (member_subset_support hA),
      Finset.sdiff_sdiff_eq_self (member_subset_support hB)] using he'
  have hdis : Disjoint F D := by
    apply Finset.disjoint_left.mpr
    intro S hS hSD
    obtain ⟨T,hT,hTS⟩ := Finset.mem_image.mp hSD
    have hh := hi S hS T hT
    rw [← hTS] at hh
    have he : (support F \ T) ∩ T = ∅ := by
      ext x; simp
    rw [he] at hh
    exact Finset.not_nonempty_empty hh
  have hsub : F ∪ D ⊆ (support F).powersetCard 3 := by
    intro S hS
    rcases Finset.mem_union.mp hS with hSF | hSD
    · exact Finset.mem_powersetCard.mpr ⟨member_subset_support hSF,hu S hSF⟩
    · obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hSD
      refine Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset,?_⟩
      rw [Finset.card_sdiff_of_subset (member_subset_support hT),hs,hu T hT]
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_union_of_disjoint hdis,hc,hDc,Finset.card_powersetCard,hs]
  decide

/-- A three-point transversal of an intersecting ten-triple design is itself a block. -/
theorem ten_three_point_transversal_iff_member
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 10)
    (C : Finset α) (hC : C.card = 3) :
    (∀ S ∈ F, (S ∩ C).Nonempty) ↔ C ∈ F := by
  classical
  constructor
  · intro hhit
    have hmin := intersecting_ten_transversal_card_ge_three F hu hf hi hc
      (C ∩ support F) (transversal_restrict_support F F C (Finset.Subset.refl _) hhit)
    have he : C ∩ support F = C := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_left (by omega)
    have hCS : C ⊆ support F := by rw [← he]; exact Finset.inter_subset_right
    have hmem : C ∈ (support F).powersetCard 3 := Finset.mem_powersetCard.mpr ⟨hCS,hC⟩
    have hpart := intersecting_six_ten_complement_partition F hu hi hc
      (intersecting_ten_design F hu hf hi hc).1
    rw [← hpart] at hmem
    rcases Finset.mem_union.mp hmem with hm | hm
    · exact hm
    · obtain ⟨S,hS,hSC⟩ := Finset.mem_image.mp hm
      have hh := hhit S hS
      rw [← hSC] at hh
      have he' : S ∩ (support F \ S) = ∅ := by ext x; simp
      rw [he'] at hh
      exact False.elim (Finset.not_nonempty_empty hh)
  · intro hC S hS
    exact hi S hS C hC

/-- Every uniform triple family crossing an extremal intersecting design
is a subfamily of that same design. -/
theorem triples_cross_ten_design_subset
    {α : Type*} [DecidableEq α] (F G : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 10)
    (huG : ∀ S ∈ G, S.card = 3)
    (hcross : ∀ S ∈ F, ∀ T ∈ G, (S ∩ T).Nonempty) : G ⊆ F := by
  intro T hT
  exact (ten_three_point_transversal_iff_member F hu hf hi hc T (huG T hT)).mp
    (fun S hS => hcross S hS T hT)

/-- At any anchor, three distinct singleton traces cannot share a residual. -/
theorem no_common_singleton_residual_at_anchor
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α)
    (a b c : α) (haR : a ∈ R) (hbR : b ∈ R) (hcR : c ∈ R)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hf : IsSunflowerFree F 3) (P : Finset α)
    (ha : P ∈ residualLink (exactTrace F R {a}) {a})
    (hb : P ∈ residualLink (exactTrace F R {b}) {b})
    (hc : P ∈ residualLink (exactTrace F R {c}) {c}) : False := by
  have hd := residual_exact_trace_disjoint_anchor F R {a} P ha
  have haP : a ∉ P := fun h => Finset.disjoint_left.mp hd h haR
  have hbP : b ∉ P := fun h => Finset.disjoint_left.mp hd h hbR
  have hcP : c ∉ P := fun h => Finset.disjoint_left.mp hd h hcR
  have haF : insert a P ∈ F := by
    have hm : insert a P ∈ exactTrace F R {a} := by simpa using core_union_residual_mem_family ha
    exact (Finset.mem_filter.mp hm).1
  have hbF : insert b P ∈ F := by
    have hm : insert b P ∈ exactTrace F R {b} := by simpa using core_union_residual_mem_family hb
    exact (Finset.mem_filter.mp hm).1
  have hcF : insert c P ∈ F := by
    have hm : insert c P ∈ exactTrace F R {c} := by simpa using core_union_residual_mem_family hc
    exact (Finset.mem_filter.mp hm).1
  have habS : insert a P ≠ insert b P := by
    intro he
    have hm : a ∈ insert b P := he ▸ Finset.mem_insert_self a P
    simp [hab,haP] at hm
  have hacS : insert a P ≠ insert c P := by
    intro he
    have hm : a ∈ insert c P := he ▸ Finset.mem_insert_self a P
    simp [hac,haP] at hm
  have hbcS : insert b P ≠ insert c P := by
    intro he
    have hm : b ∈ insert c P := he ▸ Finset.mem_insert_self b P
    simp [hbc,hbP] at hm
  have habI : insert a P ∩ insert b P = P := by ext x; simp only [Finset.mem_inter,Finset.mem_insert]; aesop
  have hacI : insert a P ∩ insert c P = P := by ext x; simp only [Finset.mem_inter,Finset.mem_insert]; aesop
  have hbcI : insert b P ∩ insert c P = P := by ext x; simp only [Finset.mem_inter,Finset.mem_insert]; aesop
  exact hf {insert a P,insert b P,insert c P}
    (by intro S hS; simp only [Finset.mem_insert,Finset.mem_singleton] at hS; rcases hS with rfl | rfl | rfl <;> assumption)
    (sunflower_three_of_intersections _ _ _ P habS hacS hbcS habI hacI hbcI)

/-- A saturated singleton-trace design contains every other singleton residue. -/
theorem rank_four_singleton_residual_subset_of_ten
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α)
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hR : R ∈ F)
    (x y : α) (hxy : x ≠ y) (hc : (exactTrace F R {x}).card = 10) :
    residualLink (exactTrace F R {y}) {y} ⊆ residualLink (exactTrace F R {x}) {x} := by
  apply triples_cross_ten_design_subset
    (residualLink (exactTrace F R {x}) {x}) (residualLink (exactTrace F R {y}) {y})
  · simpa using residualLink_uniform (core := {x}) (fun S hS => hu S (Finset.mem_filter.mp hS).1)
  · exact exact_trace_residual_free F R {x} 3 hf
  · exact exact_trace_residual_intersecting F R {x} 4 hR hu hf (by simp)
  · simpa [exact_trace_card_residual] using hc
  · simpa using residualLink_uniform (core := {y}) (fun S hS => hu S (Finset.mem_filter.mp hS).1)
  · exact disjoint_traces_residual_cross_intersect F R {x} {y} hi (by simp [Ne.symm hxy])

/-- One saturated singleton trace limits the total of all four singleton traces to twenty. -/
theorem rank_four_singleton_sum_le_twenty_of_ten
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (a b c d : α) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hR : {a,b,c,d} ∈ F)
    (hc : (exactTrace F {a,b,c,d} {a}).card = 10) :
    (exactTrace F {a,b,c,d} {a}).card + (exactTrace F {a,b,c,d} {b}).card +
      (exactTrace F {a,b,c,d} {c}).card + (exactTrace F {a,b,c,d} {d}).card ≤ 20 := by
  let G := fun x => residualLink (exactTrace F {a,b,c,d} {x}) {x}
  have hBA : G b ⊆ G a := rank_four_singleton_residual_subset_of_ten F {a,b,c,d} hu hf hi hR a b hab hc
  have hCA : G c ⊆ G a := rank_four_singleton_residual_subset_of_ten F {a,b,c,d} hu hf hi hR a c hac hc
  have hDA : G d ⊆ G a := rank_four_singleton_residual_subset_of_ten F {a,b,c,d} hu hf hi hR a d had hc
  have hBC : Disjoint (G b) (G c) := by
    apply Finset.disjoint_left.mpr
    intro P hP hQ
    exact no_common_singleton_residual_at_anchor F {a,b,c,d} a b c (by simp) (by simp) (by simp)
      hab hac hbc hf P (hBA hP) hP hQ
  have hBD : Disjoint (G b) (G d) := by
    apply Finset.disjoint_left.mpr
    intro P hP hQ
    exact no_common_singleton_residual_at_anchor F {a,b,c,d} a b d (by simp) (by simp) (by simp)
      hab had hbd hf P (hBA hP) hP hQ
  have hCD : Disjoint (G c) (G d) := by
    apply Finset.disjoint_left.mpr
    intro P hP hQ
    exact no_common_singleton_residual_at_anchor F {a,b,c,d} a c d (by simp) (by simp) (by simp)
      hac had hcd hf P (hCA hP) hP hQ
  have hsum := Finset.card_le_card (Finset.union_subset (Finset.union_subset hBA hCA) hDA)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hBD,hCD⟩),
    Finset.card_union_of_disjoint hBC] at hsum
  have hsum' : (exactTrace F {a,b,c,d} {b}).card + (exactTrace F {a,b,c,d} {c}).card +
      (exactTrace F {a,b,c,d} {d}).card ≤ 10 := by
    simpa [G,exact_trace_card_residual,hc] using hsum
  omega

/-- Outside its saturated singleton component, a member through x must also
contain every other anchor point with a nonempty singleton trace. -/
theorem saturated_point_member_contains_active_singleton
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α)
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hR : R ∈ F)
    (x y : α) (hxR : x ∈ R) (hxy : x ≠ y)
    (hc : (exactTrace F R {x}).card = 10)
    (hy : (exactTrace F R {y}).Nonempty)
    (S : Finset α) (hS : S ∈ F) (hxS : x ∈ S) (hmulti : S ∩ R ≠ {x}) : y ∈ S := by
  classical
  let L := residualLink F {x}
  let H := residualLink (exactTrace F R {x}) {x}
  let P := S \ {x}
  have hLu : ∀ T ∈ L, T.card = 3 := by
    simpa [L] using residualLink_uniform (core := {x}) hu
  have hLf : IsSunflowerFree L 3 := residualLink_sunflowerFree hf
  have hHL : H ⊆ L := by
    intro Q hQ
    obtain ⟨T,hT,hxT,hTQ⟩ := mem_residualLink_iff.mp hQ
    exact mem_residualLink_iff.mpr ⟨T,(Finset.mem_filter.mp hT).1,hxT,hTQ⟩
  have hHi : ∀ A ∈ H, ∀ B ∈ H, (A ∩ B).Nonempty :=
    exact_trace_residual_intersecting F R {x} 4 hR hu hf (by simp)
  have hHc : H.card = 10 := by simpa [H,exact_trace_card_residual] using hc
  have hPL : P ∈ L := mem_residualLink_iff.mpr ⟨S,hS,by simp [hxS],rfl⟩
  have hPH : P ∉ H := by
    intro hP
    have hm : {x} ∪ P ∈ exactTrace F R {x} := core_union_residual_mem_family hP
    have he : {x} ∪ P = S := Finset.union_sdiff_of_subset (by simp [hxS])
    rw [he] at hm
    exact hmulti (Finset.mem_filter.mp hm).2
  have hdis := Erdos20DesignSeparation.outside_intersecting_ten_disjoint_support
    L H hLu hLf hHL hHi hHc P hPL hPH
  have hGyn : (residualLink (exactTrace F R {y}) {y}).Nonempty :=
    Finset.card_pos.mp (by simpa [exact_trace_card_residual] using Finset.card_pos.mpr hy)
  obtain ⟨Q,hQ⟩ := hGyn
  have hQH : Q ∈ H := rank_four_singleton_residual_subset_of_ten F R hu hf hi hR x y hxy hc hQ
  have hT : {y} ∪ Q ∈ F := (Finset.mem_filter.mp (core_union_residual_mem_family hQ)).1
  obtain ⟨z,hz⟩ := hi S hS ({y} ∪ Q) hT
  obtain ⟨hzS,hzT⟩ := Finset.mem_inter.mp hz
  rcases Finset.mem_union.mp hzT with hzy | hzQ
  · have he : z = y := Finset.mem_singleton.mp hzy
    exact he ▸ hzS
  · have hzP : z ∈ P := by
      apply Finset.mem_sdiff.mpr
      refine ⟨hzS,?_⟩
      intro he
      have he' : z = x := Finset.mem_singleton.mp he
      subst z
      exact Finset.disjoint_left.mp (residual_exact_trace_disjoint_anchor F R {y} Q hQ) hzQ hxR
    exact False.elim (Finset.disjoint_left.mp hdis hzP (member_subset_support hQH hzQ))

/-- A non-singleton trace containing the saturated point is incompatible with
an omitted active singleton trace. This includes both pair and triple traces. -/
theorem saturated_trace_or_omitted_singleton_empty
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R C : Finset α)
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hR : R ∈ F)
    (x y : α) (hxR : x ∈ R) (hyR : y ∈ R) (hxy : x ≠ y)
    (hc : (exactTrace F R {x}).card = 10)
    (hxC : x ∈ C) (hyC : y ∉ C) (hC : C ≠ {x}) :
    (exactTrace F R C).card = 0 ∨ (exactTrace F R {y}).card = 0 := by
  by_cases hzero : (exactTrace F R C).card = 0
  · exact Or.inl hzero
  right
  by_contra hn
  obtain ⟨S,hS⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hzero)
  obtain ⟨hSF,hSR⟩ := Finset.mem_filter.mp hS
  have hxS : x ∈ S := Finset.mem_of_mem_inter_left (hSR ▸ hxC)
  have hmulti : S ∩ R ≠ {x} := by rwa [hSR]
  have hyS := saturated_point_member_contains_active_singleton F R hu hf hi hR x y hxR hxy hc
    (Finset.card_pos.mp (Nat.pos_of_ne_zero hn)) S hSF hxS hmulti
  apply hyC
  rw [← hSR]
  exact Finset.mem_inter.mpr ⟨hyS,hyR⟩

end Erdos20V8Stability
