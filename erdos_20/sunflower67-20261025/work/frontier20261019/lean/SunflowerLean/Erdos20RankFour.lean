import SunflowerLean.Erdos20SharpTwenty
import SunflowerLean.Erdos20MixedCross
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Finite rank-four bounds from exact traces and intersecting residuals. -/
namespace Erdos20RankFour
open Erdos20BCWConditional Erdos20StrictCore Erdos20RankThree
open Erdos20CrossBounds Erdos20Incidence Erdos20SharpTwenty Erdos20SharpTriples

/-- Exact singleton traces on a four-set have intersecting triple residues. -/
theorem singleton_trace_card_le_ten {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (R C : Finset α) (hR : R ∈ F)
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hC : C.card = 1) : (exactTrace F R C).card ≤ 10 := by
  have hne : C ≠ R := by intro h; have := hu R hR; rw [← h] at this; omega
  have hur : ∀ P ∈ residualLink (exactTrace F R C) C, P.card = 3 := by
    simpa [hC] using residualLink_uniform
      (fun S hS => hu S (Finset.mem_filter.mp hS).1) (core := C)
  rw [← exact_trace_card_residual]
  apply intersecting_rank_three_card_le_ten _ hur
    (exact_trace_residual_free F R C 3 hf)
  intro P hP Q hQ
  by_cases hpq : P = Q
  · subst Q
    rw [Finset.inter_self]
    exact Finset.card_pos.mp (by rw [hur P hP]; decide)
  · exact exact_trace_residuals_intersect F R C hR hf hne P Q hP hQ hpq

/-- A rank-four point degree is bounded by the sharp triple theorem. -/
theorem rank_four_degree_le_twenty {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S ∈ F, S.card = 4)
    (hf : IsSunflowerFree F 3) (x : α) :
    (F.filter (fun S => x ∈ S)).card ≤ 20 := by
  have hb := rank_three_three_petals_card_le_twenty (residualLink F {x})
    (by simpa using (residualLink_uniform (core := {x}) hu))
    (residualLink_sunflowerFree hf)
  simpa [card_residualLink, upperStar] using hb

/-- At most forty members have singleton intersection with an anchor four-set. -/
theorem singleton_intersection_card_le_forty
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3) :
    (F.filter (fun S => (S ∩ R).card = 1)).card ≤ 40 := by
  classical
  have hs : F.filter (fun S => (S ∩ R).card = 1) ⊆
      R.biUnion (fun x => exactTrace F R {x}) := by
    intro S hS
    obtain ⟨hSF,hSR⟩ := Finset.mem_filter.mp hS
    obtain ⟨x,hx⟩ := Finset.card_eq_one.mp hSR
    have hxR : x ∈ R := by
      have hxSR : x ∈ S ∩ R := by rw [hx]; simp
      exact (Finset.mem_inter.mp hxSR).2
    exact Finset.mem_biUnion.mpr ⟨x,hxR,Finset.mem_filter.mpr ⟨hSF,hx⟩⟩
  calc
    _ ≤ (R.biUnion (fun x => exactTrace F R {x})).card := Finset.card_le_card hs
    _ ≤ ∑ x ∈ R, (exactTrace F R {x}).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ R, 10 := Finset.sum_le_sum
      (fun x _ => singleton_trace_card_le_ten F R {x} hR hu hf (by simp))
    _ = 40 := by simp [hu R hR]

/-- Refining incidence by singleton intersections counts the anchor's two-unit excess. -/
theorem meeting_incidence_singleton_defect
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α)
    (hR : R ∈ F) (hR4 : R.card = 4)
    (hhit : ∀ S ∈ F, (S ∩ R).Nonempty) :
    2 * F.card + 2 ≤ (∑ x ∈ R, (F.filter (fun S => x ∈ S)).card) +
      (F.filter (fun S => (S ∩ R).card = 1)).card := by
  classical
  have hs : (∑ S ∈ F, (2 + if S = R then 2 else 0)) ≤
      ∑ S ∈ F, ((S ∩ R).card + if (S ∩ R).card = 1 then 1 else 0) := by
    apply Finset.sum_le_sum
    intro S hS
    by_cases he : S = R
    · subst S
      simp [hR4]
    · have hp := (hhit S hS).card_pos
      by_cases h1 : (S ∩ R).card = 1
      · simp [he,h1]
      · simp [he,h1]; omega
  have hsumR : (∑ S ∈ F, if S = R then 2 else 0) = 2 := by simp [hR]
  have hsum1 : (∑ S ∈ F, if (S ∩ R).card = 1 then 1 else 0) =
      (F.filter (fun S => (S ∩ R).card = 1)).card := by simp
  simp only [Finset.sum_add_distrib] at hs
  rw [hsumR,hsum1,incidence_sum_eq] at hs
  simpa [Nat.mul_comm] using hs

/-- The members meeting any anchor four-set number at most fifty-nine. -/
theorem meeting_neighborhood_card_le_fifty_nine
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3) :
    (F.filter (fun S => (S ∩ R).Nonempty)).card ≤ 59 := by
  classical
  let N := F.filter (fun S => (S ∩ R).Nonempty)
  have hRN : R ∈ N := Finset.mem_filter.mpr ⟨hR,by
    rw [Finset.inter_self]; exact Finset.card_pos.mp (by rw [hu R hR]; decide)⟩
  have huN : ∀ S ∈ N, S.card = 4 := fun S hS => hu S (Finset.mem_filter.mp hS).1
  have hfN : IsSunflowerFree N 3 := fun H hH hsun =>
    hf H (hH.trans (Finset.filter_subset _ _)) hsun
  have hdef := meeting_incidence_singleton_defect N R hRN (hu R hR)
    (fun S hS => (Finset.mem_filter.mp hS).2)
  have hsingle := singleton_intersection_card_le_forty N R hRN huN hfN
  have hsum : (∑ x ∈ R, (N.filter (fun S => x ∈ S)).card) ≤ 80 := by
    calc
      _ ≤ ∑ _x ∈ R, 20 := Finset.sum_le_sum (fun x _ => rank_four_degree_le_twenty N huN hfN x)
      _ = 80 := by simp [hu R hR]
  change N.card ≤ 59
  omega

/-- Proper exact traces have intersecting nonempty residual families. -/
theorem exact_trace_residual_intersecting
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R C : Finset α)
    (r : ℕ) (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = r)
    (hf : IsSunflowerFree F 3) (hCr : C.card < r) :
    ∀ P ∈ residualLink (exactTrace F R C) C,
      ∀ Q ∈ residualLink (exactTrace F R C) C, (P ∩ Q).Nonempty := by
  intro P hP Q hQ
  by_cases he : P = Q
  · subst Q
    rw [Finset.inter_self]
    have hc := residualLink_uniform
      (fun S hS => hu S (Finset.mem_filter.mp hS).1) (core := C) P hP
    exact Finset.card_pos.mp (by omega)
  · apply exact_trace_residuals_intersect F R C hR hf _ P Q hP hQ he
    intro h
    have hc := hu R hR
    rw [← h] at hc
    omega

/-- Disjoint anchor traces yield cross-intersecting residuals in an intersecting family. -/
theorem disjoint_traces_residual_cross_intersect
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R C D : Finset α)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hCD : Disjoint C D) :
    ∀ P ∈ residualLink (exactTrace F R C) C,
      ∀ Q ∈ residualLink (exactTrace F R D) D, (P ∩ Q).Nonempty := by
  intro P hP Q hQ
  obtain ⟨S,hS,hCS,hSP⟩ := mem_residualLink_iff.mp hP
  obtain ⟨T,hT,hDT,hTQ⟩ := mem_residualLink_iff.mp hQ
  obtain ⟨hSF,hSR⟩ := Finset.mem_filter.mp hS
  obtain ⟨hTF,hTR⟩ := Finset.mem_filter.mp hT
  obtain ⟨x,hx⟩ := hi S hSF T hTF
  obtain ⟨hxS,hxT⟩ := Finset.mem_inter.mp hx
  have hxout : x ∉ R := by
    intro hxR
    have hxC : x ∈ C := by rw [← hSR]; exact Finset.mem_inter.mpr ⟨hxS,hxR⟩
    have hxD : x ∈ D := by rw [← hTR]; exact Finset.mem_inter.mpr ⟨hxT,hxR⟩
    exact Finset.disjoint_left.mp hCD hxC hxD
  have hCR : C ⊆ R := by rw [← hSR]; exact Finset.inter_subset_right
  have hDR : D ⊆ R := by rw [← hTR]; exact Finset.inter_subset_right
  refine ⟨x,Finset.mem_inter.mpr ⟨?_,?_⟩⟩
  · rw [← hSP]; exact Finset.mem_sdiff.mpr ⟨hxS,fun hxC => hxout (hCR hxC)⟩
  · rw [← hTQ]; exact Finset.mem_sdiff.mpr ⟨hxT,fun hxD => hxout (hDR hxD)⟩

/-- A three-point trace on an anchor four-set has at most one member. -/
theorem triple_trace_card_le_one
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R C : Finset α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hCR : C ⊆ R) (hC : C.card = 3) : (exactTrace F R C).card ≤ 1 := by
  have hRnot : R ∉ exactTrace F R C := by
    intro h
    have he : R = C := by simpa using (Finset.mem_filter.mp h).2
    have := hu R hR
    rw [he] at this
    omega
  have hs : insert R (exactTrace F R C) ⊆ Erdos20Research.extensionStar F C := by
    intro S hS
    apply Erdos20Research.mem_extensionStar_iff.mpr
    rcases Finset.mem_insert.mp hS with rfl | hS
    · exact ⟨hR,hCR⟩
    · obtain ⟨hSF,hi⟩ := Finset.mem_filter.mp hS
      exact ⟨hSF,by rw [← hi]; exact Finset.inter_subset_left⟩
  have hlo := Finset.card_le_card hs
  rw [Finset.card_insert_of_notMem hRnot] at hlo
  have hhi := Erdos20Research.extensionStar_card_lt F C 4 3 hu hf (by omega)
  omega

/-- A nonempty opposite triple trace forces a common point in the singleton residue. -/
theorem singleton_triple_trace_weighted_le_ten
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R C : Finset α) (x : α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4)
    (hf : IsSunflowerFree F 3) (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (hCR : C ⊆ R) (hC : C.card = 3) (hxC : x ∉ C) :
    (exactTrace F R {x}).card + 4 * (exactTrace F R C).card ≤ 10 := by
  have hcap := triple_trace_card_le_one F R C hR hu hf hCR hC
  by_cases he : (residualLink (exactTrace F R C) C).Nonempty
  · obtain ⟨Q,hQ⟩ := he
    have hQ1 : Q.card = 1 := by
      simpa [hC] using residualLink_uniform
        (fun S hS => hu S (Finset.mem_filter.mp hS).1) (core := C) Q hQ
    obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hQ1
    let H := residualLink (exactTrace F R {x}) {x}
    have huH : ∀ P ∈ H, P.card = 3 := by
      simpa [H] using residualLink_uniform
        (fun S hS => hu S (Finset.mem_filter.mp hS).1) (core := {x})
    have hfH : IsSunflowerFree H 3 := exact_trace_residual_free F R {x} 3 hf
    have hcommon : ∀ P ∈ H, v ∈ P := by
      intro P hP
      have hcross := disjoint_traces_residual_cross_intersect F R {x} C hi
        (by simpa using hxC) P hP Q hQ
      obtain ⟨z,hz⟩ := hcross
      have hzv : z = v := by simpa [hv] using (Finset.mem_inter.mp hz).2
      exact hzv ▸ (Finset.mem_inter.mp hz).1
    have hfilter : H.filter (fun P => v ∈ P) = H := Finset.filter_eq_self.mpr hcommon
    have hb := Erdos20RankThreeEven.rank_three_degree_le_six H huH hfH v
    rw [hfilter] at hb
    change (residualLink (exactTrace F R {x}) {x}).card ≤ 6 at hb
    rw [exact_trace_card_residual] at hb
    omega
  · have hz : (exactTrace F R C).card = 0 := by
      rw [← exact_trace_card_residual]
      exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp he)
    have hb := singleton_trace_card_le_ten F R {x} hR hu hf (by simp)
    omega

/-- Exact traces partition a family. -/
theorem card_eq_sum_exact_traces
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α) :
    F.card = ∑ C ∈ R.powerset, (exactTrace F R C).card := by
  classical
  exact Finset.card_eq_sum_card_fiberwise
    (fun S _ => Finset.mem_powerset.mpr Finset.inter_subset_right)

/-- In an intersecting family the empty trace is absent. -/
theorem empty_trace_card_eq_zero
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α)
    (hR : R ∈ F) (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) :
    (exactTrace F R ∅).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  obtain ⟨hSF,hSR⟩ := Finset.mem_filter.mp hS
  have hn := hi S hSF R hR
  rw [hSR] at hn
  exact Finset.not_nonempty_empty hn

/-- A full trace in a uniform family is exactly the anchor. -/
theorem full_trace_card_eq_one
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α)
    (r : ℕ) (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = r) :
    (exactTrace F R R).card = 1 := by
  have he : exactTrace F R R = {R} := by
    ext S
    simp only [exactTrace,Finset.mem_filter,Finset.mem_singleton]
    constructor
    · rintro ⟨hSF,hSR⟩
      have hRS : R ⊆ S := by rw [← hSR]; exact Finset.inter_subset_left
      exact (Finset.eq_of_subset_of_card_le hRS (by rw [hu R hR,hu S hSF])).symm
    · rintro rfl
      exact ⟨hR,Finset.inter_self _⟩
  simp [he]

/-- An explicit four-point trace sum, used only for finite linear counting. -/
theorem sum_powerset_four
    {α : Type*} [DecidableEq α] (f : Finset α → ℕ) (x y z w : α)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    (∑ C ∈ ({x,y,z,w} : Finset α).powerset, f C) =
      f ∅ + f {x} + f {y} + f {z} + f {w} +
      f {x,y} + f {x,z} + f {x,w} + f {y,z} + f {y,w} + f {z,w} +
      f {x,y,z} + f {x,y,w} + f {x,z,w} + f {y,z,w} + f {x,y,z,w} := by
  have hsingle (g : Finset α → ℕ) :
      (∑ C ∈ ({w} : Finset α).powerset, g C) = g ∅ + g {w} := by
    change (∑ C ∈ (insert w (∅ : Finset α)).powerset, g C) = _
    rw [Finset.sum_powerset_insert (by simp)]
    simp
  simp [Finset.sum_powerset_insert,hxy,hxz,hxw,hyz,hyw,hzw,hsingle]
  omega

/-- Opposite singleton and pair traces satisfy a weighted mixed-rank bound. -/
theorem singleton_pair_trace_weighted_le_twelve
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R C : Finset α) (x : α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4)
    (hf : IsSunflowerFree F 3) (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (hC : C.card = 2) (hxC : x ∉ C) :
    (exactTrace F R {x}).card + 2 * (exactTrace F R C).card ≤ 12 := by
  have huH : ∀ P ∈ residualLink (exactTrace F R {x}) {x}, P.card = 3 := by
    simpa using residualLink_uniform
      (fun S hS => hu S (Finset.mem_filter.mp hS).1) (core := {x})
  have huG : ∀ P ∈ residualLink (exactTrace F R C) C, P.card = 2 := by
    simpa [hC] using residualLink_uniform
      (fun S hS => hu S (Finset.mem_filter.mp hS).1) (core := C)
  have hb := Erdos20MixedCross.intersecting_triples_cross_edges_weighted
    (residualLink (exactTrace F R {x}) {x}) (residualLink (exactTrace F R C) C)
    huH (exact_trace_residual_free F R {x} 3 hf)
    (exact_trace_residual_intersecting F R {x} 4 hR hu hf (by simp))
    huG (exact_trace_residual_free F R C 3 hf)
    (exact_trace_residual_intersecting F R C 4 hR hu hf (by omega))
    (disjoint_traces_residual_cross_intersect F R {x} C hi (by simpa using hxC))
  simpa only [exact_trace_card_residual] using hb

/-- Weighted opposite-trace inequalities improve the intersecting rank-four bound. -/
theorem intersecting_rank_four_card_le_forty_seven
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) : F.card ≤ 47 := by
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
    have hp (a : α) (C : Finset α) (hC : C.card = 2) (haC : a ∉ C) :
        n {a} + 2 * n C ≤ 12 :=
      singleton_pair_trace_weighted_le_twelve F {x,y,z,w} C a hR hu hf hi hC haC
    have ht (a : α) (C : Finset α) (hC : C.card = 3)
        (hCR : C ⊆ ({x,y,z,w} : Finset α)) (haC : a ∉ C) :
        n {a} + 4 * n C ≤ 10 :=
      singleton_triple_trace_weighted_le_ten F {x,y,z,w} C a hR hu hf hi hCR hC haC
    have hp1 := hp x {y,z} (by simp [hyz]) (by simp [hxy,hxz])
    have hp2 := hp x {y,w} (by simp [hyw]) (by simp [hxy,hxw])
    have hp3 := hp x {z,w} (by simp [hzw]) (by simp [hxz,hxw])
    have hp4 := hp y {x,z} (by simp [hxz]) (by simp [Ne.symm hxy,hyz])
    have hp5 := hp y {x,w} (by simp [hxw]) (by simp [Ne.symm hxy,hyw])
    have hp6 := hp y {z,w} (by simp [hzw]) (by simp [hyz,hyw])
    have hp7 := hp z {x,y} (by simp [hxy]) (by simp [Ne.symm hxz,Ne.symm hyz])
    have hp8 := hp z {x,w} (by simp [hxw]) (by simp [Ne.symm hxz,hzw])
    have hp9 := hp z {y,w} (by simp [hyw]) (by simp [Ne.symm hyz,hzw])
    have hp10 := hp w {x,y} (by simp [hxy]) (by simp [Ne.symm hxw,Ne.symm hyw])
    have hp11 := hp w {x,z} (by simp [hxz]) (by simp [Ne.symm hxw,Ne.symm hzw])
    have hp12 := hp w {y,z} (by simp [hyz]) (by simp [Ne.symm hyw,Ne.symm hzw])
    have ht1 := ht x {y,z,w} (by simp [hyz,hyw,hzw]) (by simp) (by simp [hxy,hxz,hxw])
    have ht2 := ht y {x,z,w} (by simp [hxz,hxw,hzw]) (by simp [Finset.insert_subset_iff]) (by simp [Ne.symm hxy,hyz,hyw])
    have ht3 := ht z {x,y,w} (by simp [hxy,hxw,hyw]) (by simp [Finset.insert_subset_iff]) (by simp [Ne.symm hxz,Ne.symm hyz,hzw])
    have ht4 := ht w {x,y,z} (by simp [hxy,hxz,hyz]) (by simp [Finset.insert_subset_iff]) (by simp [Ne.symm hxw,Ne.symm hyw,Ne.symm hzw])
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

/-- The rank-four graph degree is exactly the number of disjoint members. -/
theorem rank_four_disjointnessGraph_degree_eq {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S ∈ F, S.card = 4) (R : F) :
    (disjointnessGraph F).degree R = (F.filter (fun S => S ∩ R.val = ∅)).card := by
  classical
  rw [SimpleGraph.degree]
  have he : ((disjointnessGraph F).neighborFinset R).image Subtype.val =
      F.filter (fun S => S ∩ R.val = ∅) := by
    ext S
    simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset, Finset.mem_filter]
    constructor
    · rintro ⟨T, hT, rfl⟩
      exact ⟨T.property, by simpa [Finset.inter_comm] using hT.2⟩
    · rintro ⟨hSF, hi⟩
      refine ⟨⟨S,hSF⟩, ?_, rfl⟩
      change R ≠ ⟨S,hSF⟩ ∧ R.val ∩ S = ∅
      refine ⟨?_, by simpa [Finset.inter_comm] using hi⟩
      intro heq
      have hev : R.val = S := congrArg Subtype.val heq
      have hzero : S = ∅ := by simpa [hev] using hi
      have hc := hu S hSF
      simp [hzero] at hc
  rw [← he, Finset.card_image_of_injective _ Subtype.val_injective]


theorem rank_four_card_le_ninety_four_of_two_colorable
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hcol : (disjointnessGraph F).Colorable 2) : F.card ≤ 94 := by
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
  have hcap : ∀ i, (classes i).card ≤ 47 := by
    intro i
    apply intersecting_rank_four_card_le_forty_seven _
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
    _ ≤ ∑ _i : Fin 2, 47 := Finset.sum_le_sum (fun i _ => hcap i)
    _ = 94 := by simp

/-- The trace and mixed-rank estimates give an unconditional upper bound ninety-eight. -/
theorem rank_four_card_le_ninety_eight
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3) : F.card ≤ 98 := by
  classical
  by_contra hnot
  have hlarge : 99 ≤ F.card := by omega
  have hne : F.Nonempty := Finset.card_pos.mp (by omega)
  letI : Nonempty F := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  have hmin : F.card - 59 ≤ (disjointnessGraph F).minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro R
    rw [rank_four_disjointnessGraph_degree_eq F hu R]
    have hN := meeting_neighborhood_card_le_fifty_nine F R.val R.property hu hf
    have hs := Finset.filter_card_add_filter_neg_card_eq_card
      (s := F) (p := fun S => (S ∩ R.val).Nonempty)
    simp only [Finset.not_nonempty_iff_eq_empty] at hs
    omega
  have hcol : (disjointnessGraph F).Colorable 2 := by
    apply SimpleGraph.colorable_of_cliqueFree_lt_minDegree
      (disjointnessGraph_triangle_free F hf)
    have hcard : Fintype.card F = F.card := Fintype.card_coe _
    simp only [hcard]
    omega
  have h94 := rank_four_card_le_ninety_four_of_two_colorable F hu hf hcol
  omega

end Erdos20RankFour
