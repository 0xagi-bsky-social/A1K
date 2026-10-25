import SunflowerLean.Erdos20V5Frontier
import SunflowerLean.Erdos20RankFour

/-! Stronger intersecting rank-four bounds from exact-trace capacity deficits. -/
namespace Erdos20RankFourRefined
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20CrossBounds Erdos20RankThree Erdos20RankThreeEven
open Erdos20MixedCross Erdos20RankFour Erdos20SharpTriples

/-- The six-point design theorem excludes a two-point transversal at cardinality ten. -/
theorem intersecting_triples_cross_edge_card_le_nine
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (B : Finset α)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hB : B.card = 2)
    (hcross : ∀ S ∈ F, (S ∩ B).Nonempty) : F.card ≤ 9 := by
  have hten := intersecting_rank_three_card_le_ten F hu hf hi
  by_contra hn
  obtain ⟨S,hS,hdis⟩ := Erdos20V5Frontier.intersecting_ten_no_two_point_transversal
    F hu hf hi (by omega) B hB
  have hhit := hcross S hS
  rw [hdis] at hhit
  exact Finset.not_nonempty_empty hhit

/-- An intersecting family of at least seven triples has degree at most five. -/
theorem intersecting_triples_cross_two_edges_card_le_seven {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (B C : Finset α)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (hB : B.card = 2) (hC : C.card = 2) (hne : B ≠ C)
    (hBC : (B ∩ C).Nonempty)
    (hcrossB : ∀ S ∈ F, (S ∩ B).Nonempty)
    (hcrossC : ∀ S ∈ F, (S ∩ C).Nonempty) : F.card ≤ 7 := by
  classical
  by_cases hsmall : F.card ≤ 6
  · omega
  · obtain ⟨x,hx⟩ := hBC
    obtain ⟨hxB,hxC⟩ := Finset.mem_inter.mp hx
    obtain ⟨y,hy⟩ := Finset.card_eq_one.mp (show (B.erase x).card = 1 by
      rw [Finset.card_erase_of_mem hxB,hB])
    obtain ⟨z,hz⟩ := Finset.card_eq_one.mp (show (C.erase x).card = 1 by
      rw [Finset.card_erase_of_mem hxC,hC])
    have hBs : B = {x,y} := by rw [← Finset.insert_erase hxB,hy]
    have hCs : C = {x,z} := by rw [← Finset.insert_erase hxC,hz]
    have hyz : y ≠ z := by intro he; apply hne; rw [hBs,hCs,he]
    have hcover : F ⊆ (F.filter (fun S => x ∈ S)) ∪
        (F.filter (fun S => ({y,z} : Finset α) ⊆ S)) := by
      intro S hS
      by_cases hxS : x ∈ S
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hS,hxS⟩)
      · have hyS : y ∈ S := by
          obtain ⟨a,ha⟩ := hcrossB S hS
          obtain ⟨haS,haB⟩ := Finset.mem_inter.mp ha
          simp only [hBs,Finset.mem_insert,Finset.mem_singleton] at haB
          rcases haB with rfl | rfl
          · exact False.elim (hxS haS)
          · exact haS
        have hzS : z ∈ S := by
          obtain ⟨a,ha⟩ := hcrossC S hS
          obtain ⟨haS,haC⟩ := Finset.mem_inter.mp ha
          simp only [hCs,Finset.mem_insert,Finset.mem_singleton] at haC
          rcases haC with rfl | rfl
          · exact False.elim (hxS haS)
          · exact haS
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨hS,by simp [Finset.insert_subset_iff,hyS,hzS]⟩)
    have ha := Finset.card_le_card hcover
    have hb := Finset.card_union_le (F.filter (fun S => x ∈ S))
      (F.filter (fun S => ({y,z} : Finset α) ⊆ S))
    have hd := Erdos20ExtremalStructure.intersecting_card_ge_seven_degree_le_five F hu hf hi (by omega) x
    have hp := triple_pair_degree_le_two F hu hf {y,z} (by simp [hyz])
    omega


/-- A size-sensitive strengthening of the mixed triple/edge capacity bound. -/
theorem intersecting_triples_cross_edges_weighted_twenty_one
    {α : Type*} [DecidableEq α] (F G : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (huG : ∀ S ∈ G, S.card = 2) (hfG : IsSunflowerFree G 3)
    (hiG : ∀ S ∈ G, ∀ T ∈ G, (S ∩ T).Nonempty)
    (hcross : ∀ S ∈ F, ∀ T ∈ G, (S ∩ T).Nonempty) :
    2 * F.card + 3 * G.card ≤ 21 := by
  have hF := intersecting_rank_three_card_le_ten F hu hf hi
  have hG := intersecting_rank_two_three_petals_card_le_three G huG hfG hiG
  by_cases h0 : G.card = 0
  · omega
  by_cases h1 : G.card = 1
  · obtain ⟨B,hB⟩ := Finset.card_pos.mp (show 0 < G.card by omega)
    have h9 := intersecting_triples_cross_edge_card_le_nine F B hu hf hi (huG B hB)
      (fun S hS => hcross S hS B hB)
    omega
  by_cases h2 : G.card = 2
  · obtain ⟨B,C,hBC,hshape⟩ := Finset.card_eq_two.mp h2
    have hB : B ∈ G := by simp [hshape]
    have hC : C ∈ G := by simp [hshape]
    have h7 := intersecting_triples_cross_two_edges_card_le_seven F B C hu hf hi
      (huG B hB) (huG C hC) hBC (hiG B hB C hC)
      (fun S hS => hcross S hS B hB) (fun S hS => hcross S hS C hC)
    omega
  have h6 := triples_cross_triangle_card_le_six F G hu hf huG hfG hiG (by omega) hcross
  omega

/-- A common point and three cross-intersecting edges leave at most four triples. -/
theorem common_point_triples_cross_three_edges_card_le_four
    {α : Type*} [DecidableEq α] (F G : Finset (Finset α)) (v : α)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (huG : ∀ S ∈ G, S.card = 2) (hfG : IsSunflowerFree G 3)
    (hcG : G.card = 3) (hcommon : ∀ S ∈ F, v ∈ S)
    (hcross : ∀ S ∈ F, ∀ T ∈ G, (S ∩ T).Nonempty) : F.card ≤ 4 := by
  classical
  have hex : ∃ B ∈ G, v ∉ B := by
    by_contra hn
    push_neg at hn
    have hle := common_point_rank_two_three_petals_card_le_two G huG hfG v hn
    omega
  obtain ⟨B,hB,hvB⟩ := hex
  let H := residualLink F {v}
  have huH : ∀ P ∈ H, P.card = 2 := by
    simpa [H] using residualLink_uniform (core := {v}) hu
  have hfH : IsSunflowerFree H 3 := residualLink_sunflowerFree hf
  have hcrossH : ∀ P ∈ H, (P ∩ B).Nonempty := by
    intro P hP
    have hSP := core_union_residual_mem_family hP
    obtain ⟨x,hx⟩ := hcross ({v} ∪ P) hSP B hB
    obtain ⟨hxS,hxB⟩ := Finset.mem_inter.mp hx
    have hxP : x ∈ P := by
      rcases Finset.mem_union.mp hxS with hxv | hxP
      · have he : x = v := Finset.mem_singleton.mp hxv
        exact False.elim (hvB (he ▸ hxB))
      · exact hxP
    exact ⟨x,Finset.mem_inter.mpr ⟨hxP,hxB⟩⟩
  have hle := cross_intersecting_card_le H B 2 hcrossH
    (rank_two_three_petals_degree_le_two H huH hfH)
  have hstar : upperStar F {v} = F := by
    ext S
    simp only [upperStar,Finset.mem_filter,Finset.singleton_subset_iff]
    exact and_iff_left_of_imp (hcommon S)
  have hc : H.card = F.card := by
    change (residualLink F {v}).card = F.card
    rw [card_residualLink,hstar]
  rw [hc,huG B hB] at hle
  exact hle


/-- The common-point case has a stronger weighted capacity. -/
theorem common_point_triples_cross_edges_weighted_eighteen
    {α : Type*} [DecidableEq α] (F G : Finset (Finset α)) (v : α)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (huG : ∀ S ∈ G, S.card = 2) (hfG : IsSunflowerFree G 3)
    (hiG : ∀ S ∈ G, ∀ T ∈ G, (S ∩ T).Nonempty)
    (hcommon : ∀ S ∈ F, v ∈ S)
    (hcross : ∀ S ∈ F, ∀ T ∈ G, (S ∩ T).Nonempty) :
    2 * F.card + 3 * G.card ≤ 18 := by
  have he : F.filter (fun S => v ∈ S) = F := Finset.filter_eq_self.mpr hcommon
  have hF := rank_three_degree_le_six F hu hf v
  rw [he] at hF
  have hG := intersecting_rank_two_three_petals_card_le_three G huG hfG hiG
  by_cases h2 : G.card ≤ 2
  · omega
  have h4 := common_point_triples_cross_three_edges_card_le_four F G v hu hf huG hfG
    (by omega) hcommon hcross
  omega

/-- Three disjoint-trace capacities are coupled by the common residual point. -/
theorem singleton_pair_triple_trace_weighted_le_twenty_one
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R C D : Finset α) (x : α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4)
    (hf : IsSunflowerFree F 3) (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (hC : C.card = 2) (hxC : x ∉ C)
    (hDR : D ⊆ R) (hD : D.card = 3) (hxD : x ∉ D) :
    2 * (exactTrace F R {x}).card + 3 * (exactTrace F R C).card +
      3 * (exactTrace F R D).card ≤ 21 := by
  let H := residualLink (exactTrace F R {x}) {x}
  let G := residualLink (exactTrace F R C) C
  have huH : ∀ P ∈ H, P.card = 3 := by
    simpa [H] using residualLink_uniform
      (fun S hS => hu S (Finset.mem_filter.mp hS).1) (core := {x})
  have huG : ∀ P ∈ G, P.card = 2 := by
    simpa [G,hC] using residualLink_uniform
      (fun S hS => hu S (Finset.mem_filter.mp hS).1) (core := C)
  have hfH : IsSunflowerFree H 3 := exact_trace_residual_free F R {x} 3 hf
  have hfG : IsSunflowerFree G 3 := exact_trace_residual_free F R C 3 hf
  have hiH : ∀ P ∈ H, ∀ Q ∈ H, (P ∩ Q).Nonempty :=
    exact_trace_residual_intersecting F R {x} 4 hR hu hf (by simp)
  have hiG : ∀ P ∈ G, ∀ Q ∈ G, (P ∩ Q).Nonempty :=
    exact_trace_residual_intersecting F R C 4 hR hu hf (by omega)
  have hcross : ∀ P ∈ H, ∀ Q ∈ G, (P ∩ Q).Nonempty :=
    disjoint_traces_residual_cross_intersect F R {x} C hi (by simpa using hxC)
  have hcH : H.card = (exactTrace F R {x}).card := exact_trace_card_residual F R {x}
  have hcG : G.card = (exactTrace F R C).card := exact_trace_card_residual F R C
  have hcap := triple_trace_card_le_one F R D hR hu hf hDR hD
  by_cases he : (residualLink (exactTrace F R D) D).Nonempty
  · obtain ⟨Q,hQ⟩ := he
    have hQ1 : Q.card = 1 := by
      simpa [hD] using residualLink_uniform
        (fun S hS => hu S (Finset.mem_filter.mp hS).1) (core := D) Q hQ
    obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hQ1
    have hcommon : ∀ P ∈ H, v ∈ P := by
      intro P hP
      obtain ⟨z,hz⟩ := disjoint_traces_residual_cross_intersect F R {x} D hi
        (by simpa using hxD) P hP Q hQ
      have hzv : z = v := by simpa [hv] using (Finset.mem_inter.mp hz).2
      exact hzv ▸ (Finset.mem_inter.mp hz).1
    have hb := common_point_triples_cross_edges_weighted_eighteen H G v huH hfH
      huG hfG hiG hcommon hcross
    rw [hcH,hcG] at hb
    omega
  · have hz : (exactTrace F R D).card = 0 := by
      rw [← exact_trace_card_residual]
      exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp he)
    have hb := intersecting_triples_cross_edges_weighted_twenty_one H G huH hfH hiH
      huG hfG hiG hcross
    rw [hcH,hcG] at hb
    omega

/-- Coupling singleton, pair and triple traces improves the intersecting bound to forty-three. -/
theorem intersecting_rank_four_card_le_forty_three
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) : F.card ≤ 43 := by
  classical
  by_cases hne : F.Nonempty
  · obtain ⟨R,hR⟩ := hne
    obtain ⟨x,y,z,w,hxy,hxz,hxw,hyz,hyw,hzw,hshape⟩ := Finset.card_eq_four.mp (hu R hR)
    subst R
    let n : Finset α → ℕ := fun C => (exactTrace F {x,y,z,w} C).card
    have hpart := card_eq_sum_exact_traces F {x,y,z,w}
    change F.card = ∑ C ∈ ({x,y,z,w} : Finset α).powerset, n C at hpart
    rw [sum_powerset_four n x y z w hxy hxz hxw hyz hyw hzw] at hpart
    have h0 : n ∅ = 0 := empty_trace_card_eq_zero F {x,y,z,w} hR hi
    have h4 : n {x,y,z,w} = 1 := full_trace_card_eq_one F {x,y,z,w} 4 hR hu
    have hp (a : α) (C D : Finset α) (hC : C.card = 2) (haC : a ∉ C)
        (hD : D.card = 3) (hDR : D ⊆ ({x,y,z,w} : Finset α)) (haD : a ∉ D) :
        2 * n {a} + 3 * n C + 3 * n D ≤ 21 :=
      singleton_pair_triple_trace_weighted_le_twenty_one F {x,y,z,w} C D a
        hR hu hf hi hC haC hDR hD haD
    have hp1 := hp x {y,z} {y,z,w} (by simp [hyz]) (by simp [hxy,hxz]) (by simp [hyz,hyw,hzw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [hxy,hxz,hxw])
    have hp2 := hp x {y,w} {y,z,w} (by simp [hyw]) (by simp [hxy,hxw]) (by simp [hyz,hyw,hzw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [hxy,hxz,hxw])
    have hp3 := hp x {z,w} {y,z,w} (by simp [hzw]) (by simp [hxz,hxw]) (by simp [hyz,hyw,hzw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [hxy,hxz,hxw])
    have hp4 := hp y {x,z} {x,z,w} (by simp [hxz]) (by simp [Ne.symm hxy,hyz]) (by simp [hxz,hxw,hzw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxy,hyz,hyw])
    have hp5 := hp y {x,w} {x,z,w} (by simp [hxw]) (by simp [Ne.symm hxy,hyw]) (by simp [hxz,hxw,hzw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxy,hyz,hyw])
    have hp6 := hp y {z,w} {x,z,w} (by simp [hzw]) (by simp [hyz,hyw]) (by simp [hxz,hxw,hzw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxy,hyz,hyw])
    have hp7 := hp z {x,y} {x,y,w} (by simp [hxy]) (by simp [Ne.symm hxz,Ne.symm hyz]) (by simp [hxy,hxw,hyw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxz,Ne.symm hyz,hzw])
    have hp8 := hp z {x,w} {x,y,w} (by simp [hxw]) (by simp [Ne.symm hxz,hzw]) (by simp [hxy,hxw,hyw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxz,Ne.symm hyz,hzw])
    have hp9 := hp z {y,w} {x,y,w} (by simp [hyw]) (by simp [Ne.symm hyz,hzw]) (by simp [hxy,hxw,hyw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxz,Ne.symm hyz,hzw])
    have hp10 := hp w {x,y} {x,y,z} (by simp [hxy]) (by simp [Ne.symm hxw,Ne.symm hyw]) (by simp [hxy,hxz,hyz]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxw,Ne.symm hyw,Ne.symm hzw])
    have hp11 := hp w {x,z} {x,y,z} (by simp [hxz]) (by simp [Ne.symm hxw,Ne.symm hzw]) (by simp [hxy,hxz,hyz]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxw,Ne.symm hyw,Ne.symm hzw])
    have hp12 := hp w {y,z} {x,y,z} (by simp [hyz]) (by simp [Ne.symm hyw,Ne.symm hzw]) (by simp [hxy,hxz,hyz]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxw,Ne.symm hyw,Ne.symm hzw])
    have hsum := (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hp1 hp2) hp3) hp4) hp5) hp6) hp7) hp8) hp9) hp10) hp11) hp12)
    clear hp hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]


/-- Point degree can be recovered from the exact anchor traces that contain the point. -/
theorem degree_eq_sum_exact_traces
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α) (x : α)
    (hxR : x ∈ R) :
    (F.filter (fun S => x ∈ S)).card =
      ∑ C ∈ R.powerset, if x ∈ C then (exactTrace F R C).card else 0 := by
  classical
  rw [card_eq_sum_exact_traces (F.filter (fun S => x ∈ S)) R]
  apply Finset.sum_congr rfl
  intro C hC
  by_cases hxC : x ∈ C
  · have he : exactTrace (F.filter (fun S => x ∈ S)) R C = exactTrace F R C := by
      ext S
      simp only [exactTrace,Finset.mem_filter]
      constructor
      · rintro ⟨⟨hSF,_⟩,hSC⟩
        exact ⟨hSF,hSC⟩
      · rintro ⟨hSF,hSC⟩
        have hxS : x ∈ S := Finset.mem_of_mem_inter_left (hSC ▸ hxC)
        exact ⟨⟨hSF,hxS⟩,hSC⟩
    simp [hxC,he]
  · have he : exactTrace (F.filter (fun S => x ∈ S)) R C = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      obtain ⟨hSfil,hSC⟩ := Finset.mem_filter.mp hS
      obtain ⟨hSF,hxS⟩ := Finset.mem_filter.mp hSfil
      exact hxC (hSC ▸ Finset.mem_inter.mpr ⟨hxS,hxR⟩)
    simp [hxC,he]

/-- A pair trace on a four-set has at most three intersecting edge residues. -/
theorem pair_trace_card_le_three
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R C : Finset α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hC : C.card = 2) : (exactTrace F R C).card ≤ 3 := by
  rw [← exact_trace_card_residual]
  apply intersecting_rank_two_three_petals_card_le_three
  · simpa [hC] using residualLink_uniform
      (fun S hS => hu S (Finset.mem_filter.mp hS).1) (core := C)
  · exact exact_trace_residual_free F R C 3 hf
  · exact exact_trace_residual_intersecting F R C 4 hR hu hf (by omega)

private theorem saturated_twelve (a b c d e f g h i j k l : ℕ)
    (ha : a ≤ 21) (hb : b ≤ 21) (hc : c ≤ 21) (hd : d ≤ 21)
    (he : e ≤ 21) (hf : f ≤ 21) (hg : g ≤ 21) (hh : h ≤ 21)
    (hi : i ≤ 21) (hj : j ≤ 21) (hk : k ≤ 21) (hl : l ≤ 21)
    (hs : a+b+c+d+e+f+g+h+i+j+k+l = 252) :
    a=21 ∧ b=21 ∧ c=21 ∧ d=21 ∧ e=21 ∧ f=21 ∧ g=21 ∧ h=21 ∧
      i=21 ∧ j=21 ∧ k=21 ∧ l=21 := by omega

set_option maxHeartbeats 500000 in
/-- Equality at forty-three forces a constant degree thirteen or sixteen on each member. -/
theorem forty_three_member_degree_pattern
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 43)
    (R : Finset α) (hR : R ∈ F) :
    ∃ d, (d = 13 ∨ d = 16) ∧ ∀ u ∈ R, (F.filter (fun S => u ∈ S)).card = d := by
  classical
  obtain ⟨x,y,z,w,hxy,hxz,hxw,hyz,hyw,hzw,hshape⟩ := Finset.card_eq_four.mp (hu R hR)
  subst R
  let n : Finset α → ℕ := fun C => (exactTrace F {x,y,z,w} C).card
  have hpart := card_eq_sum_exact_traces F {x,y,z,w}
  change F.card = ∑ C ∈ ({x,y,z,w} : Finset α).powerset, n C at hpart
  rw [sum_powerset_four n x y z w hxy hxz hxw hyz hyw hzw] at hpart
  have h0 : n ∅ = 0 := empty_trace_card_eq_zero F {x,y,z,w} hR hi
  have h4 : n {x,y,z,w} = 1 := full_trace_card_eq_one F {x,y,z,w} 4 hR hu
  have hp (a : α) (C D : Finset α) (hC : C.card = 2) (haC : a ∉ C)
      (hD : D.card = 3) (hDR : D ⊆ ({x,y,z,w} : Finset α)) (haD : a ∉ D) :
      2 * n {a} + 3 * n C + 3 * n D ≤ 21 :=
    singleton_pair_triple_trace_weighted_le_twenty_one F {x,y,z,w} C D a
      hR hu hf hi hC haC hDR hD haD
  have hp1 := hp x {y,z} {y,z,w} (by simp [hyz]) (by simp [hxy,hxz]) (by simp [hyz,hyw,hzw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [hxy,hxz,hxw])
  have hp2 := hp x {y,w} {y,z,w} (by simp [hyw]) (by simp [hxy,hxw]) (by simp [hyz,hyw,hzw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [hxy,hxz,hxw])
  have hp3 := hp x {z,w} {y,z,w} (by simp [hzw]) (by simp [hxz,hxw]) (by simp [hyz,hyw,hzw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [hxy,hxz,hxw])
  have hp4 := hp y {x,z} {x,z,w} (by simp [hxz]) (by simp [Ne.symm hxy,hyz]) (by simp [hxz,hxw,hzw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxy,hyz,hyw])
  have hp5 := hp y {x,w} {x,z,w} (by simp [hxw]) (by simp [Ne.symm hxy,hyw]) (by simp [hxz,hxw,hzw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxy,hyz,hyw])
  have hp6 := hp y {z,w} {x,z,w} (by simp [hzw]) (by simp [hyz,hyw]) (by simp [hxz,hxw,hzw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxy,hyz,hyw])
  have hp7 := hp z {x,y} {x,y,w} (by simp [hxy]) (by simp [Ne.symm hxz,Ne.symm hyz]) (by simp [hxy,hxw,hyw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxz,Ne.symm hyz,hzw])
  have hp8 := hp z {x,w} {x,y,w} (by simp [hxw]) (by simp [Ne.symm hxz,hzw]) (by simp [hxy,hxw,hyw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxz,Ne.symm hyz,hzw])
  have hp9 := hp z {y,w} {x,y,w} (by simp [hyw]) (by simp [Ne.symm hyz,hzw]) (by simp [hxy,hxw,hyw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxz,Ne.symm hyz,hzw])
  have hp10 := hp w {x,y} {x,y,z} (by simp [hxy]) (by simp [Ne.symm hxw,Ne.symm hyw]) (by simp [hxy,hxz,hyz]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxw,Ne.symm hyw,Ne.symm hzw])
  have hp11 := hp w {x,z} {x,y,z} (by simp [hxz]) (by simp [Ne.symm hxw,Ne.symm hzw]) (by simp [hxy,hxz,hyz]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxw,Ne.symm hyw,Ne.symm hzw])
  have hp12 := hp w {y,z} {x,y,z} (by simp [hyz]) (by simp [Ne.symm hyw,Ne.symm hzw]) (by simp [hxy,hxz,hyz]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxw,Ne.symm hyw,Ne.symm hzw])
  have hsum := (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hp1 hp2) hp3) hp4) hp5) hp6) hp7) hp8) hp9) hp10) hp11) hp12)
  have ht0 : n {x,y,z} = 0 ∧ n {x,y,w} = 0 ∧ n {x,z,w} = 0 ∧ n {y,z,w} = 0 := by
    omega
  obtain ⟨ht1,ht2,ht3,ht4⟩ := ht0
  have hsumEq : (2 * n {x} + 3 * n {y,z} + 3 * n {y,z,w}) + (2 * n {x} + 3 * n {y,w} + 3 * n {y,z,w}) + (2 * n {x} + 3 * n {z,w} + 3 * n {y,z,w}) + (2 * n {y} + 3 * n {x,z} + 3 * n {x,z,w}) + (2 * n {y} + 3 * n {x,w} + 3 * n {x,z,w}) + (2 * n {y} + 3 * n {z,w} + 3 * n {x,z,w}) + (2 * n {z} + 3 * n {x,y} + 3 * n {x,y,w}) + (2 * n {z} + 3 * n {x,w} + 3 * n {x,y,w}) + (2 * n {z} + 3 * n {y,w} + 3 * n {x,y,w}) + (2 * n {w} + 3 * n {x,y} + 3 * n {x,y,z}) + (2 * n {w} + 3 * n {x,z} + 3 * n {x,y,z}) + (2 * n {w} + 3 * n {y,z} + 3 * n {x,y,z}) = 252 := by omega
  obtain ⟨he1,he2,he3,he4,he5,he6,he7,he8,he9,he10,he11,he12⟩ :=
    saturated_twelve _ _ _ _ _ _ _ _ _ _ _ _ hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hsumEq
  have hpair := pair_trace_card_le_three F {x,y,z,w} {y,z} hR hu hf (by simp [hyz])
  change n {y,z} ≤ 3 at hpair
  have hdx := degree_eq_sum_exact_traces F {x,y,z,w} x (by simp)
  change (F.filter (fun S => x ∈ S)).card = ∑ C ∈ ({x,y,z,w} : Finset α).powerset, if x ∈ C then n C else 0 at hdx
  rw [sum_powerset_four _ x y z w hxy hxz hxw hyz hyw hzw] at hdx
  simp [hxy,hxz,hxw] at hdx
  have hdy := degree_eq_sum_exact_traces F {x,y,z,w} y (by simp)
  change (F.filter (fun S => y ∈ S)).card = ∑ C ∈ ({x,y,z,w} : Finset α).powerset, if y ∈ C then n C else 0 at hdy
  rw [sum_powerset_four _ x y z w hxy hxz hxw hyz hyw hzw] at hdy
  simp [Ne.symm hxy,hyz,hyw] at hdy
  have hdz := degree_eq_sum_exact_traces F {x,y,z,w} z (by simp)
  change (F.filter (fun S => z ∈ S)).card = ∑ C ∈ ({x,y,z,w} : Finset α).powerset, if z ∈ C then n C else 0 at hdz
  rw [sum_powerset_four _ x y z w hxy hxz hxw hyz hyw hzw] at hdz
  simp [Ne.symm hxz,Ne.symm hyz,hzw] at hdz
  have hdw := degree_eq_sum_exact_traces F {x,y,z,w} w (by simp)
  change (F.filter (fun S => w ∈ S)).card = ∑ C ∈ ({x,y,z,w} : Finset α).powerset, if w ∈ C then n C else 0 at hdw
  rw [sum_powerset_four _ x y z w hxy hxz hxw hyz hyw hzw] at hdw
  simp [Ne.symm hxw,Ne.symm hyw,Ne.symm hzw] at hdw
  clear hp hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hsum hsumEq hpart
  have hs : n {x} = 9 ∨ n {x} = 6 := by omega
  rcases hs with hs | hs
  · refine ⟨13,Or.inl rfl,?_⟩
    intro u huR
    simp only [Finset.mem_insert,Finset.mem_singleton] at huR
    rcases huR with rfl | rfl | rfl | rfl <;> omega
  · refine ⟨16,Or.inr rfl,?_⟩
    intro u huR
    simp only [Finset.mem_insert,Finset.mem_singleton] at huR
    rcases huR with rfl | rfl | rfl | rfl <;> omega

/-- Intersection propagates the equality degree, contradicting total incidence 172. -/
theorem intersecting_rank_four_card_le_forty_two
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) : F.card ≤ 42 := by
  classical
  have h43 := intersecting_rank_four_card_le_forty_three F hu hf hi
  by_contra hn
  have hc : F.card = 43 := by omega
  obtain ⟨R,hR⟩ := Finset.card_pos.mp (show 0 < F.card by omega)
  obtain ⟨d,hd,hRdeg⟩ := forty_three_member_degree_pattern F hu hf hi hc R hR
  have hall : ∀ x ∈ support F, (F.filter (fun S => x ∈ S)).card = d := by
    intro x hx
    obtain ⟨S,hS,hxS⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨e,he,hSdeg⟩ := forty_three_member_degree_pattern F hu hf hi hc S hS
    obtain ⟨v,hv⟩ := hi S hS R hR
    have hde : e = d := (hSdeg v (Finset.mem_inter.mp hv).1).symm.trans
      (hRdeg v (Finset.mem_inter.mp hv).2)
    exact (hSdeg x hxS).trans hde
  have hsum := Erdos20ExtremalSupport.support_degree_sum F 4 hu
  have he : (∑ x ∈ support F, (F.filter (fun S => x ∈ S)).card) = (support F).card * d := by
    calc
      _ = ∑ _x ∈ support F, d := Finset.sum_congr rfl hall
      _ = _ := by simp
  rw [he,hc] at hsum
  rcases hd with rfl | rfl <;> omega

/-- Two intersecting color classes each satisfy the refined upper bound. -/
theorem rank_four_card_le_eighty_four_of_two_colorable
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hcol : (disjointnessGraph F).Colorable 2) : F.card ≤ 84 := by
  classical
  obtain ⟨c⟩ := hcol
  let classes : Fin 2 → Finset (Finset α) := fun i =>
    (Finset.univ.filter (fun S : F => c S = i)).image Subtype.val
  have hmem : ∀ i S, S ∈ classes i ↔ ∃ hS : S ∈ F, c ⟨S,hS⟩ = i := by
    intro i S
    simp only [classes, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨T, hi, rfl⟩
      exact ⟨T.property, hi⟩
    · rintro ⟨hS, hi⟩
      exact ⟨⟨S,hS⟩, hi, rfl⟩
  have hsub : ∀ i, classes i ⊆ F := by
    intro i S hS
    exact ((hmem i S).mp hS).choose
  have hcap : ∀ i, (classes i).card ≤ 42 := by
    intro i
    apply intersecting_rank_four_card_le_forty_two _
      (fun S hS => hu S (hsub i hS))
      (fun H hH hsun => hf H (hH.trans (hsub i)) hsun)
    intro S hS T hT
    obtain ⟨hSF, hcS⟩ := (hmem i S).mp hS
    obtain ⟨hTF, hcT⟩ := (hmem i T).mp hT
    by_contra hnot
    have hi : S ∩ T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    have hne : (⟨S,hSF⟩ : F) ≠ ⟨T,hTF⟩ := by
      intro heq
      have hv : S = T := congrArg Subtype.val heq
      have he : S = ∅ := by simpa [← hv] using hi
      have hs3 := hu S hSF
      simp [he] at hs3
    exact c.valid (show (disjointnessGraph F).Adj ⟨S,hSF⟩ ⟨T,hTF⟩ from ⟨hne,hi⟩)
      (hcS.trans hcT.symm)
  have hcover : F ⊆ Finset.univ.biUnion classes := by
    intro S hS
    exact Finset.mem_biUnion.mpr ⟨c ⟨S,hS⟩, Finset.mem_univ _,
      (hmem _ S).mpr ⟨hS,rfl⟩⟩
  calc
    _ ≤ (Finset.univ.biUnion classes).card := Finset.card_le_card hcover
    _ ≤ ∑ i, (classes i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin 2, 42 := Finset.sum_le_sum (fun i _ => hcap i)
    _ = 84 := by simp


end Erdos20RankFourRefined
