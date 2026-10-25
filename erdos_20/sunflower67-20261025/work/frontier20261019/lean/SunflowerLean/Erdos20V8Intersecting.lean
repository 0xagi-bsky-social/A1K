import SunflowerLean.Erdos20ExtremalTransversals
import SunflowerLean.Erdos20RankFourRefined

/-! Transversal-sensitive constraints for intersecting sunflower-free families. -/
namespace Erdos20V8Intersecting
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20CrossBounds Erdos20RankThree Erdos20RankFour Erdos20MixedCross
open Erdos20DesignSeparation Erdos20ExtremalTransversals

/-- Membership in precisely one point of a pair identifies its exact trace. -/
theorem inter_pair_eq_singleton {α : Type*} [DecidableEq α]
    (S : Finset α) (a b : α) (ha : a ∈ S) (hb : b ∉ S) :
    S ∩ {a,b} = {a} := by
  ext x
  simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨hx,rfl | rfl⟩
    · rfl
    · exact False.elim (hb hx)
  · rintro rfl
    exact ⟨ha,Or.inl rfl⟩

/-- Two cross-intersecting singleton residues contribute at most six triples;
the remaining pair star contributes at most two. -/
theorem intersecting_triples_two_point_transversal_card_le_eight
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (C : Finset α)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hC : C.card = 2)
    (hhit : ∀ S ∈ F, (S ∩ C).Nonempty) : F.card ≤ 8 := by
  classical
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hC
  let A := exactTrace F {a,b} {a}
  let B := exactTrace F {a,b} {b}
  let P := F.filter (fun S => ({a,b} : Finset α) ⊆ S)
  have hAu : ∀ S ∈ residualLink A {a}, S.card = 2 := by
    simpa using residualLink_uniform (core := {a})
      (fun S (hS : S ∈ A) => hu S (Finset.mem_filter.mp hS).1)
  have hBu : ∀ S ∈ residualLink B {b}, S.card = 2 := by
    simpa using residualLink_uniform (core := {b})
      (fun S (hS : S ∈ B) => hu S (Finset.mem_filter.mp hS).1)
  have hAf : IsSunflowerFree (residualLink A {a}) 3 := exact_trace_residual_free F {a,b} {a} 3 hf
  have hBf : IsSunflowerFree (residualLink B {b}) 3 := exact_trace_residual_free F {a,b} {b} 3 hf
  have hcross := disjoint_traces_residual_cross_intersect F {a,b} {a} {b} hi (by simpa using Ne.symm hab)
  have hAB := cross_intersecting_rank_two_joint_card_le_six
    (residualLink A {a}) (residualLink B {b}) hAu hAf hBu hBf hcross
  change (residualLink (exactTrace F {a,b} {a}) {a}).card +
    (residualLink (exactTrace F {a,b} {b}) {b}).card ≤ 6 at hAB
  rw [exact_trace_card_residual,exact_trace_card_residual] at hAB
  have hP : P.card ≤ 2 := triple_pair_degree_le_two F hu hf {a,b} (by simp [hab])
  have hcover : F ⊆ (A ∪ B) ∪ P := by
    intro S hS
    by_cases ha : a ∈ S
    · by_cases hb : b ∈ S
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨hS,by simp [Finset.insert_subset_iff,ha,hb]⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hS,inter_pair_eq_singleton S a b ha hb⟩))
    · have hb : b ∈ S := by
        obtain ⟨x,hx⟩ := hhit S hS
        obtain ⟨hxS,hxC⟩ := Finset.mem_inter.mp hx
        simp only [Finset.mem_insert,Finset.mem_singleton] at hxC
        rcases hxC with rfl | rfl
        · exact False.elim (ha hxS)
        · exact hxS
      have he : S ∩ ({a,b} : Finset α) = {b} := by
        rw [Finset.pair_comm a b]
        exact inter_pair_eq_singleton S b a hb ha
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hS,he⟩))
  have hc := Finset.card_le_card hcover
  have hc1 := Finset.card_union_le (A ∪ B) P
  have hc2 := Finset.card_union_le A B
  change A.card + B.card ≤ 6 at hAB
  omega

/-- An intersecting triple family of size at least nine avoids every given pair. -/
theorem intersecting_nine_avoids_pair
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (C : Finset α)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (hc : 9 ≤ F.card) (hC : C.card = 2) : ∃ S ∈ F, S ∩ C = ∅ := by
  classical
  by_contra hn
  push_neg at hn
  have hb := intersecting_triples_two_point_transversal_card_le_eight F C hu hf hi hC hn
  omega

/-- Every transversal of an intersecting family of at least nine triples has size at least three. -/
theorem intersecting_nine_transversal_card_ge_three
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (C : Finset α)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (hc : 9 ≤ F.card) (hhit : ∀ S ∈ F, (S ∩ C).Nonempty) : 3 ≤ C.card := by
  have hd : ∀ x, (F.filter (fun S => x ∈ S)).card ≤ 5 :=
    Erdos20ExtremalStructure.intersecting_card_ge_seven_degree_le_five F hu hf hi (by omega)
  have hlo := cross_intersecting_card_le F C 5 hhit hd
  by_contra hn
  have hC : C.card = 2 := by omega
  have h8 := intersecting_triples_two_point_transversal_card_le_eight F C hu hf hi hC hhit
  omega

/-- The sharp nonempty mixed envelope: triple and edge counts sum to at most nine. -/
theorem intersecting_triples_cross_nonempty_edges_sum_le_nine
    {α : Type*} [DecidableEq α] (F G : Finset (Finset α))
    (huF : ∀ S ∈ F, S.card = 3) (hfF : IsSunflowerFree F 3)
    (hiF : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (huG : ∀ S ∈ G, S.card = 2) (hfG : IsSunflowerFree G 3)
    (hiG : ∀ S ∈ G, ∀ T ∈ G, (S ∩ T).Nonempty) (hG : G.Nonempty)
    (hcross : ∀ S ∈ F, ∀ T ∈ G, (S ∩ T).Nonempty) : F.card + G.card ≤ 9 := by
  have hG3 := intersecting_rank_two_three_petals_card_le_three G huG hfG hiG
  by_cases hG1 : G.card = 1
  · obtain ⟨B,hB⟩ := hG
    have hF8 := intersecting_triples_two_point_transversal_card_le_eight F B huF hfF hiF
      (huG B hB) (fun S hS => hcross S hS B hB)
    omega
  by_cases hG2 : G.card = 2
  · obtain ⟨B,C,hBC,hshape⟩ := Finset.card_eq_two.mp hG2
    have hB : B ∈ G := by rw [hshape]; simp
    have hC : C ∈ G := by rw [hshape]; simp
    have hF7 := Erdos20RankFourRefined.intersecting_triples_cross_two_edges_card_le_seven
      F B C huF hfF hiF (huG B hB) (huG C hC) hBC (hiG B hB C hC)
      (fun S hS => hcross S hS B hB) (fun S hS => hcross S hS C hC)
    omega
  · have hcard : G.card = 3 := by have := hG.card_pos; omega
    have hF6 := triples_cross_triangle_card_le_six F G huF hfF huG hfG hiG hcard hcross
    omega

/-- The nonempty mixed envelope strengthens the old weighted bound by its exact small-count deficit. -/
theorem intersecting_triples_cross_nonempty_edges_weighted
    {α : Type*} [DecidableEq α] (F G : Finset (Finset α))
    (huF : ∀ S ∈ F, S.card = 3) (hfF : IsSunflowerFree F 3)
    (hiF : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (huG : ∀ S ∈ G, S.card = 2) (hfG : IsSunflowerFree G 3)
    (hiG : ∀ S ∈ G, ∀ T ∈ G, (S ∩ T).Nonempty) (hG : G.Nonempty)
    (hcross : ∀ S ∈ F, ∀ T ∈ G, (S ∩ T).Nonempty) :
    2 * F.card + 3 * G.card ≤ 18 + G.card := by
  have h := intersecting_triples_cross_nonempty_edges_sum_le_nine
    F G huF hfF hiF huG hfG hiG hG hcross
  omega

/-- An eight-member example attaining the two-point-transversal bound. -/
def eightPairTransversal : Finset (Finset (Fin 7)) :=
  {{0,2,3},{0,2,4},{0,3,4},{1,2,3},{1,2,4},{1,3,4},{0,1,5},{0,1,6}}

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Exact sharpness data are checked on all ordered triples of the eight displayed members. -/
theorem eight_pair_transversal_witness :
    eightPairTransversal.card = 8 ∧
    (∀ S ∈ eightPairTransversal, S.card = 3) ∧ IsSunflowerFree eightPairTransversal 3 ∧
    (∀ S ∈ eightPairTransversal, ∀ T ∈ eightPairTransversal, (S ∩ T).Nonempty) ∧
    ∀ S ∈ eightPairTransversal, (S ∩ ({0,1} : Finset (Fin 7))).Nonempty := by
  refine ⟨by decide,?_,?_,?_,?_⟩
  · intro S hS
    simp only [eightPairTransversal,Finset.mem_insert,Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · apply Erdos20TripleWitness.sunflowerFree_of_no_triple
    intro S hS
    simp only [eightPairTransversal,Finset.mem_insert,Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      intro T hT
      simp only [eightPairTransversal,Finset.mem_insert,Finset.mem_singleton] at hT
      rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      intro U hU
      simp only [eightPairTransversal,Finset.mem_insert,Finset.mem_singleton] at hU
      rcases hU with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · intro S hS T hT
    simp only [eightPairTransversal,Finset.mem_insert,Finset.mem_singleton] at hS hT
    rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · intro S hS
    simp only [eightPairTransversal,Finset.mem_insert,Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A triple family containing an isolated ten-design and admitting a four-point
transversal has at most sixteen members. -/
theorem triples_with_ten_design_transversal_four_card_le_sixteen
    {α : Type*} [DecidableEq α] (F H : Finset (Finset α)) (C : Finset α)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (hHF : H ⊆ F)
    (hHi : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty) (hHc : H.card = 10)
    (hC : C.card ≤ 4) (hhit : ∀ S ∈ F, (S ∩ C).Nonempty) : F.card ≤ 16 := by
  classical
  have hHf : IsSunflowerFree H 3 := fun G hG hg => hf G (hG.trans hHF) hg
  have hlow := intersecting_ten_transversal_card_ge_three H
    (fun S hS => hu S (hHF hS)) hHf hHi hHc (C ∩ support H)
    (transversal_restrict_support F H C hHF hhit)
  have hpart := Finset.card_sdiff_add_card_inter C (support H)
  have hsmall : (C \ support H).card ≤ 1 := by omega
  have hKu : ∀ S ∈ F \ H, S.card = 3 := fun S hS => hu S (Finset.mem_sdiff.mp hS).1
  have hKf : IsSunflowerFree (F \ H) 3 :=
    fun G hG hg => hf G (hG.trans Finset.sdiff_subset) hg
  have hKhits : ∀ S ∈ F \ H, (S ∩ (C \ support H)).Nonempty := by
    intro S hS
    obtain ⟨hSF,hSH⟩ := Finset.mem_sdiff.mp hS
    have hd := outside_intersecting_ten_disjoint_support F H hu hf hHF hHi hHc S hSF hSH
    obtain ⟨x,hx⟩ := hhit S hSF
    obtain ⟨hxS,hxC⟩ := Finset.mem_inter.mp hx
    exact ⟨x,Finset.mem_inter.mpr ⟨hxS,Finset.mem_sdiff.mpr
      ⟨hxC,fun hxH => Finset.disjoint_left.mp hd hxS hxH⟩⟩⟩
  have hKd : ∀ x, ((F \ H).filter (fun S => x ∈ S)).card ≤ 6 :=
    Erdos20RankThreeEven.rank_three_degree_le_six (F \ H) hKu hKf
  have hbound := cross_intersecting_card_le (F \ H) (C \ support H) 6 hKhits hKd
  have hsplit := Finset.card_sdiff_add_card_eq_card hHF
  omega

/-- A member avoiding a point is a transversal of that point's residual link. -/
theorem avoiding_member_hits_point_link
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x : α) (T : Finset α)
    (hi : ∀ S ∈ F, ∀ U ∈ F, (S ∩ U).Nonempty) (hT : T ∈ F) (hxT : x ∉ T) :
    ∀ P ∈ residualLink F {x}, (P ∩ T).Nonempty := by
  intro P hP
  have hPF : {x} ∪ P ∈ F := core_union_residual_mem_family hP
  obtain ⟨y,hy⟩ := hi ({x} ∪ P) hPF T hT
  obtain ⟨hyP,hyT⟩ := Finset.mem_inter.mp hy
  rcases Finset.mem_union.mp hyP with hyx | hyP
  · have he : y = x := Finset.mem_singleton.mp hyx
    exact False.elim (hxT (he ▸ hyT))
  · exact ⟨y,Finset.mem_inter.mpr ⟨hyP,hyT⟩⟩

/-- In a nontrivial large intersecting rank-four family, a point link containing
a ten-design has degree at most sixteen, even without an extension to twenty. -/
theorem rank_four_link_with_ten_design_degree_le_sixteen
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x : α) (H : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : 21 ≤ F.card)
    (hHL : H ⊆ residualLink F {x})
    (hHi : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty) (hHc : H.card = 10) :
    (F.filter (fun S => x ∈ S)).card ≤ 16 := by
  classical
  have hd := rank_four_degree_le_twenty F hu hf x
  have hex : ∃ T ∈ F, x ∉ T := by
    by_contra hn
    push_neg at hn
    have he : F.filter (fun S => x ∈ S) = F := Finset.filter_eq_self.mpr hn
    rw [he] at hd
    omega
  obtain ⟨T,hT,hxT⟩ := hex
  have hLu : ∀ P ∈ residualLink F {x}, P.card = 3 := by
    simpa using residualLink_uniform (core := {x}) hu
  have hLf : IsSunflowerFree (residualLink F {x}) 3 := residualLink_sunflowerFree hf
  have hbound := triples_with_ten_design_transversal_four_card_le_sixteen
    (residualLink F {x}) H T hLu hLf hHL hHi hHc (by rw [hu T hT])
    (avoiding_member_hits_point_link F x T hi hT hxT)
  simpa [card_residualLink,upperStar] using hbound

/-- Degree at least seventeen excludes every intersecting ten-design from its point link. -/
theorem rank_four_large_degree_link_has_no_ten_design
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x : α)
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : 21 ≤ F.card)
    (hd : 17 ≤ (F.filter (fun S => x ∈ S)).card) :
    ¬ ∃ H ⊆ residualLink F {x}, H.card = 10 ∧
      ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty := by
  rintro ⟨H,hHL,hHc,hHi⟩
  have h := rank_four_link_with_ten_design_degree_le_sixteen F x H hu hf hi hc hHL hHi hHc
  omega

/-- Any nonempty pair trace disjoint from a singleton trace enforces the improved mixed envelope. -/
theorem rank_four_singleton_pair_trace_sum_le_nine
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R C : Finset α) (x : α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hC : C.card = 2)
    (hxC : x ∉ C) (hp : 0 < (exactTrace F R C).card) :
    (exactTrace F R {x}).card + (exactTrace F R C).card ≤ 9 := by
  let H := residualLink (exactTrace F R {x}) {x}
  let G := residualLink (exactTrace F R C) C
  have hHu : ∀ P ∈ H, P.card = 3 := by
    simpa [H] using residualLink_uniform (core := {x})
      (fun S hS => hu S (Finset.mem_filter.mp hS).1)
  have hGu : ∀ P ∈ G, P.card = 2 := by
    simpa [G,hC] using residualLink_uniform (core := C)
      (fun S hS => hu S (Finset.mem_filter.mp hS).1)
  have hHf : IsSunflowerFree H 3 := exact_trace_residual_free F R {x} 3 hf
  have hGf : IsSunflowerFree G 3 := exact_trace_residual_free F R C 3 hf
  have hHi := exact_trace_residual_intersecting F R {x} 4 hR hu hf (by simp)
  have hGi := exact_trace_residual_intersecting F R C 4 hR hu hf (by omega)
  have hG : G.Nonempty := Finset.card_pos.mp (by simpa [G,exact_trace_card_residual] using hp)
  have hcross := disjoint_traces_residual_cross_intersect F R {x} C hi (by simpa using hxC)
  have h := intersecting_triples_cross_nonempty_edges_sum_le_nine H G
    hHu hHf hHi hGu hGf hGi hG hcross
  simpa [H,G,exact_trace_card_residual] using h

/-- A singleton trace of size at least nine excludes every disjoint pair trace. -/
theorem rank_four_large_singleton_disjoint_pair_trace_empty
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R C : Finset α) (x : α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hC : C.card = 2)
    (hxC : x ∉ C) (hs : 9 ≤ (exactTrace F R {x}).card) : exactTrace F R C = ∅ := by
  apply Finset.card_eq_zero.mp
  by_contra hn
  have h := rank_four_singleton_pair_trace_sum_le_nine F R C x hR hu hf hi hC hxC (by omega)
  omega

end Erdos20V8Intersecting
