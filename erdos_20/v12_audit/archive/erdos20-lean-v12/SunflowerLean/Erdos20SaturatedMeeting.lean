import SunflowerLean.Erdos20DesignSeparation
import SunflowerLean.Erdos20ThreeCrossEdges

/-! Saturated singleton traces improve the rank-four meeting-neighborhood bound. -/
namespace Erdos20SaturatedMeeting
open Erdos20BCWConditional Erdos20StrictCore Erdos20RankThree Erdos20RankFour
open Erdos20DesignSeparation Erdos20ThreeCrossEdges Erdos20Incidence

/-- Removing a subcore from an exact-trace class preserves its cardinality. -/
theorem trace_subcore_residual_card {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (R C D : Finset α) (hDC : D ⊆ C) :
    (residualLink (exactTrace F R C) D).card = (exactTrace F R C).card := by
  rw [card_residualLink]
  congr 1
  apply Finset.filter_eq_self.mpr
  intro S hS
  have he := (Finset.mem_filter.mp hS).2
  exact hDC.trans (by rw [← he]; exact Finset.inter_subset_left)

/-- The rank-four pair trace at x,y injects, after deleting x, into the
singleton trace at y in the complement of the singleton-trace residue. -/
theorem pair_trace_card_le_complement_singleton
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α)
    (x y : α) (hxy : x ≠ y) (hyR : y ∈ R) :
    (exactTrace F R {x,y}).card ≤
      (exactTrace (residualLink F {x} \ residualLink (exactTrace F R {x}) {x})
        (R.erase x) {y}).card := by
  classical
  rw [← trace_subcore_residual_card F R {x,y} {x} (by simp)]
  apply Finset.card_le_card
  intro P hP
  obtain ⟨S,hS,hxS,hSP⟩ := mem_residualLink_iff.mp hP
  obtain ⟨hSF,hSR⟩ := Finset.mem_filter.mp hS
  have hyS : y ∈ S := by
    have hm : y ∈ S ∩ R := by rw [hSR]; simp
    exact (Finset.mem_inter.mp hm).1
  have hyP : y ∈ P := by
    rw [← hSP]
    exact Finset.mem_sdiff.mpr ⟨hyS,by simpa using Ne.symm hxy⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨?_,?_⟩,?_⟩
  · exact mem_residualLink_iff.mpr ⟨S,hSF,hxS,hSP⟩
  · intro hPH
    exact Finset.disjoint_left.mp
      (residual_exact_trace_disjoint_anchor F R {x} P hPH) hyP hyR
  · apply Finset.Subset.antisymm
    · intro z hz
      obtain ⟨hzP,hzR⟩ := Finset.mem_inter.mp hz
      rw [← hSP] at hzP
      have hzSR : z ∈ S ∩ R := Finset.mem_inter.mpr
        ⟨(Finset.mem_sdiff.mp hzP).1,(Finset.mem_erase.mp hzR).2⟩
      rw [hSR] at hzSR
      rcases Finset.mem_insert.mp hzSR with hzx | hzy
      · exact False.elim ((Finset.mem_erase.mp hzR).1 hzx)
      · exact hzy
    · intro z hz
      have hzy := Finset.mem_singleton.mp hz
      subst z
      exact Finset.mem_inter.mpr ⟨hyP,Finset.mem_erase.mpr ⟨Ne.symm hxy,hyR⟩⟩

/-- A saturated singleton trace leaves at most six incident pair-trace members. -/
theorem saturated_singleton_incident_pair_sum_le_six
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x a b c : α)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hR : {x,a,b,c} ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hs : (exactTrace F {x,a,b,c} {x}).card = 10) :
    (exactTrace F {x,a,b,c} {x,a}).card +
      (exactTrace F {x,a,b,c} {x,b}).card +
      (exactTrace F {x,a,b,c} {x,c}).card ≤ 6 := by
  classical
  let L := residualLink F {x}
  let H := residualLink (exactTrace F {x,a,b,c} {x}) {x}
  let K := L \ H
  have hLu : ∀ S ∈ L, S.card = 3 := by
    simpa [L] using residualLink_uniform (core := {x}) hu
  have hLf : IsSunflowerFree L 3 := residualLink_sunflowerFree hf
  have hHL : H ⊆ L := by
    intro P hP
    obtain ⟨S,hS,hxS,hSP⟩ := mem_residualLink_iff.mp hP
    exact mem_residualLink_iff.mpr ⟨S,(Finset.mem_filter.mp hS).1,hxS,hSP⟩
  have hHi : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty :=
    exact_trace_residual_intersecting F {x,a,b,c} {x} 4 hR hu hf (by simp)
  have hHc : H.card = 10 := by simpa [H,exact_trace_card_residual] using hs
  have hKi := complement_of_intersecting_ten_intersecting L H hLu hLf hHL hHi hHc
  have hKu : ∀ S ∈ K, S.card = 3 := fun S hS => hLu S (Finset.mem_sdiff.mp hS).1
  have hKf : IsSunflowerFree K 3 := fun G hG hg => hLf G (hG.trans Finset.sdiff_subset) hg
  have hRK : ({a,b,c} : Finset α) ∈ K := by
    apply Finset.mem_sdiff.mpr
    constructor
    · apply mem_residualLink_iff.mpr
      refine ⟨{x,a,b,c},hR,by simp,?_⟩
      ext z
      simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton]
      aesop
    · intro hm
      have hd := residual_exact_trace_disjoint_anchor F {x,a,b,c} {x} {a,b,c} hm
      exact Finset.disjoint_left.mp hd (by simp : a ∈ ({a,b,c} : Finset α)) (by simp)
  have hbnd := intersecting_triple_singleton_sum_le_six K a b c hab hac hbc hRK hKu hKf hKi
  have he : ({x,a,b,c} : Finset α).erase x = {a,b,c} := by
    ext z
    simp only [Finset.mem_erase,Finset.mem_insert,Finset.mem_singleton]
    aesop
  have ha := pair_trace_card_le_complement_singleton F {x,a,b,c} x a hxa (by simp)
  have hb := pair_trace_card_le_complement_singleton F {x,a,b,c} x b hxb (by simp)
  have hc := pair_trace_card_le_complement_singleton F {x,a,b,c} x c hxc (by simp)
  rw [he] at ha hb hc
  change (exactTrace F {x,a,b,c} {x,a}).card ≤ (exactTrace K {a,b,c} {a}).card at ha
  change (exactTrace F {x,a,b,c} {x,b}).card ≤ (exactTrace K {a,b,c} {b}).card at hb
  change (exactTrace F {x,a,b,c} {x,c}).card ≤ (exactTrace K {a,b,c} {c}).card at hc
  omega

/-- Any pair trace on a four-set has at most three members. -/
theorem rank_four_pair_trace_card_le_three
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R C : Finset α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hC : C.card = 2) : (exactTrace F R C).card ≤ 3 := by
  rw [← exact_trace_card_residual]
  exact Erdos20CrossBounds.intersecting_rank_two_three_petals_card_le_three _
    (by simpa [hC] using residualLink_uniform (core := C) (fun S hS => hu S (Finset.mem_filter.mp hS).1))
    (exact_trace_residual_free F R C 3 hf)
    (exact_trace_residual_intersecting F R C 4 hR hu hf (by omega))

/-- Singleton traces and their three incident pair traces obey a weighted bound. -/
theorem singleton_incident_pairs_weighted_le_thirty_six
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x a b c : α)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hR : {x,a,b,c} ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3) :
    3 * (exactTrace F {x,a,b,c} {x}).card +
      (exactTrace F {x,a,b,c} {x,a}).card +
      (exactTrace F {x,a,b,c} {x,b}).card +
      (exactTrace F {x,a,b,c} {x,c}).card ≤ 36 := by
  have hs := Erdos20RankFour.singleton_trace_card_le_ten F {x,a,b,c} {x} hR hu hf (by simp)
  by_cases he : (exactTrace F {x,a,b,c} {x}).card = 10
  · have hp := saturated_singleton_incident_pair_sum_le_six F x a b c hxa hxb hxc hab hac hbc hR hu hf he
    omega
  · have ha := rank_four_pair_trace_card_le_three F {x,a,b,c} {x,a} hR hu hf (by simp [hxa])
    have hb := rank_four_pair_trace_card_le_three F {x,a,b,c} {x,b} hR hu hf (by simp [hxb])
    have hc := rank_four_pair_trace_card_le_three F {x,a,b,c} {x,c} hR hu hf (by simp [hxc])
    omega

/-- Double-count anchor incidences through the exact-trace partition. -/
theorem incidence_eq_sum_weighted_exact_traces
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α) :
    (∑ x ∈ R, (F.filter (fun S => x ∈ S)).card) =
      ∑ C ∈ R.powerset, C.card * (exactTrace F R C).card := by
  classical
  rw [← incidence_sum_eq]
  symm
  calc
    _ = ∑ C ∈ R.powerset, ∑ S ∈ exactTrace F R C, (S ∩ R).card := by
      apply Finset.sum_congr rfl
      intro C _
      have he : (∑ S ∈ exactTrace F R C, (S ∩ R).card) =
          ∑ _S ∈ exactTrace F R C, C.card :=
        Finset.sum_congr rfl (fun S hS => congrArg Finset.card (Finset.mem_filter.mp hS).2)
      rw [he]
      simp [Nat.mul_comm]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun S _ => Finset.mem_powerset.mpr (Finset.inter_subset_right (s₁ := S) (s₂ := R)))
      (fun S => (S ∩ R).card)

/-- A family whose members all meet one of its four-sets has size at most fifty-seven. -/
theorem all_meeting_anchor_card_le_fifty_seven
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hhit : ∀ S ∈ F, (S ∩ R).Nonempty) : F.card ≤ 57 := by
  classical
  obtain ⟨x,y,z,w,hxy,hxz,hxw,hyz,hyw,hzw,hshape⟩ := Finset.card_eq_four.mp (hu R hR)
  subst R
  let n : Finset α → ℕ := fun C => (exactTrace F {x,y,z,w} C).card
  have hpart := card_eq_sum_exact_traces F {x,y,z,w}
  change F.card = ∑ C ∈ ({x,y,z,w} : Finset α).powerset, n C at hpart
  rw [sum_powerset_four n x y z w hxy hxz hxw hyz hyw hzw] at hpart
  have h0 : n ∅ = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro S hS
    obtain ⟨hSF,hSR⟩ := Finset.mem_filter.mp hS
    have hn := hhit S hSF
    rw [hSR] at hn
    exact Finset.not_nonempty_empty hn
  have h4 : n {x,y,z,w} = 1 := full_trace_card_eq_one F {x,y,z,w} 4 hR hu
  have heY : ({y,x,z,w} : Finset α) = {x,y,z,w} := by ext t; simp [or_left_comm]
  have heZ : ({z,x,y,w} : Finset α) = {x,y,z,w} := by ext t; simp [or_left_comm]
  have heW : ({w,x,y,z} : Finset α) = {x,y,z,w} := by ext t; simp [or_comm,or_left_comm]
  have hs1 := singleton_incident_pairs_weighted_le_thirty_six F x y z w
    hxy hxz hxw hyz hyw hzw hR hu hf
  have hs2 := singleton_incident_pairs_weighted_le_thirty_six F y x z w
    (Ne.symm hxy) hyz hyw hxz hxw hzw (by rw [heY]; exact hR) hu hf
  have hs3 := singleton_incident_pairs_weighted_le_thirty_six F z x y w
    (Ne.symm hxz) (Ne.symm hyz) hzw hxy hxw hyw (by rw [heZ]; exact hR) hu hf
  have hs4 := singleton_incident_pairs_weighted_le_thirty_six F w x y z
    (Ne.symm hxw) (Ne.symm hyw) (Ne.symm hzw) hxy hxz hyz (by rw [heW]; exact hR) hu hf
  rw [heY,Finset.pair_comm y x] at hs2
  rw [heZ,Finset.pair_comm z x,Finset.pair_comm z y] at hs3
  rw [heW,Finset.pair_comm w x,Finset.pair_comm w y,Finset.pair_comm w z] at hs4
  change 3 * n {x} + n {x,y} + n {x,z} + n {x,w} ≤ 36 at hs1
  change 3 * n {y} + n {x,y} + n {y,z} + n {y,w} ≤ 36 at hs2
  change 3 * n {z} + n {x,z} + n {y,z} + n {z,w} ≤ 36 at hs3
  change 3 * n {w} + n {x,w} + n {y,w} + n {z,w} ≤ 36 at hs4
  have ht (C : Finset α) (hC : C.card = 3) (hCR : C ⊆ ({x,y,z,w} : Finset α)) : n C ≤ 1 :=
    triple_trace_card_le_one F {x,y,z,w} C hR hu hf hCR hC
  have ht1 := ht {x,y,z} (by simp [hxy,hxz,hyz]) (by simp [Finset.insert_subset_iff])
  have ht2 := ht {x,y,w} (by simp [hxy,hxw,hyw]) (by simp [Finset.insert_subset_iff])
  have ht3 := ht {x,z,w} (by simp [hxz,hxw,hzw]) (by simp [Finset.insert_subset_iff])
  have ht4 := ht {y,z,w} (by simp [hyz,hyw,hzw]) (by simp)
  have hinc : (∑ C ∈ ({x,y,z,w} : Finset α).powerset, C.card * n C) ≤ 80 := by
    rw [← incidence_eq_sum_weighted_exact_traces F {x,y,z,w}]
    calc
      _ ≤ ∑ _t ∈ ({x,y,z,w} : Finset α), 20 :=
        Finset.sum_le_sum (fun t _ => rank_four_degree_le_twenty F hu hf t)
      _ = 80 := by simp [hxy,hxz,hxw,hyz,hyw,hzw]
  rw [sum_powerset_four (fun C => C.card * n C) x y z w hxy hxz hxw hyz hyw hzw] at hinc
  simp only [Finset.card_empty,zero_mul,Finset.card_singleton,one_mul] at hinc
  simp [hxy,hxz,hxw,hyz,hyw,hzw] at hinc
  omega

/-- Every rank-four meeting neighborhood has at most fifty-seven members. -/
theorem meeting_neighborhood_card_le_fifty_seven
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3) :
    (F.filter (fun S => (S ∩ R).Nonempty)).card ≤ 57 := by
  classical
  let N := F.filter (fun S => (S ∩ R).Nonempty)
  have hRN : R ∈ N := Finset.mem_filter.mpr ⟨hR,by
    rw [Finset.inter_self]; exact Finset.card_pos.mp (by rw [hu R hR]; decide)⟩
  exact all_meeting_anchor_card_le_fifty_seven N R hRN
    (fun S hS => hu S (Finset.mem_filter.mp hS).1)
    (fun H hH hsun => hf H (hH.trans (Finset.filter_subset _ _)) hsun)
    (fun S hS => (Finset.mem_filter.mp hS).2)

end Erdos20SaturatedMeeting
