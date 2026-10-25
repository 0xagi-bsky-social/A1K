import SunflowerLean.Erdos20V10Profile54
import SunflowerLean.Erdos20V8ProfileBridge
import SunflowerLean.Erdos20V8HighDegrees
import SunflowerLean.Erdos20V8Global
import SunflowerLean.Erdos20V8Boundary

namespace Erdos20V10Profile54Bridge
open Erdos20BCWConditional Erdos20RankThree Erdos20RankFour Erdos20RankFourRefined
open Erdos20SaturatedMeeting Erdos20SharpTriples Erdos20V8Global
open Erdos20V10Profile54 Erdos20V8ProfileBridge Erdos20V8MeetingProfile Erdos20DegreeCongruences Erdos20V8Boundary

set_option maxHeartbeats 800000 in
/-- The numerical profile is realized by the actual four point degrees. -/
theorem all_meeting_fifty_four_degree_cap_eighteen_traces
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3) (hc : 54 ≤ F.card)
    (x y z w : α) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) (hR : {x,y,z,w} ∈ F)
    (hhit : ∀ S ∈ F, (S ∩ {x,y,z,w}).Nonempty) :
    (∀ p, degree F p ≤ 18) →
    9 ≤ (exactTrace F {x,y,z,w} {x}).card ∧
    9 ≤ (exactTrace F {x,y,z,w} {y}).card ∧
    9 ≤ (exactTrace F {x,y,z,w} {z}).card ∧
    9 ≤ (exactTrace F {x,y,z,w} {w}).card ∧
    ((exactTrace F {x,y,z,w} {x}).card=10 ∨
      (exactTrace F {x,y,z,w} {y}).card=10 ∨
      (exactTrace F {x,y,z,w} {z}).card=10 ∨
      (exactTrace F {x,y,z,w} {w}).card=10) := by
  intro hd
  classical
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
  have hb1 : n {x,y} ≤ 3 := pair_trace_card_le_three F {x,y,z,w} {x,y} hR hu hf (by simp [hxy])
  have hb2 : n {x,z} ≤ 3 := pair_trace_card_le_three F {x,y,z,w} {x,z} hR hu hf (by simp [hxz])
  have hb3 : n {x,w} ≤ 3 := pair_trace_card_le_three F {x,y,z,w} {x,w} hR hu hf (by simp [hxw])
  have hb4 : n {y,z} ≤ 3 := pair_trace_card_le_three F {x,y,z,w} {y,z} hR hu hf (by simp [hyz])
  have hb5 : n {y,w} ≤ 3 := pair_trace_card_le_three F {x,y,z,w} {y,w} hR hu hf (by simp [hyw])
  have hb6 : n {z,w} ≤ 3 := pair_trace_card_le_three F {x,y,z,w} {z,w} hR hu hf (by simp [hzw])
  have hc1 : n {y,z,w} ≤ 1 := triple_trace_card_le_one F {x,y,z,w} {y,z,w} hR hu hf (by simp) (by simp [hyz,hyw,hzw])
  have hc2 : n {x,z,w} ≤ 1 := triple_trace_card_le_one F {x,y,z,w} {x,z,w} hR hu hf (by simp [Finset.insert_subset_iff]) (by simp [hxz,hxw,hzw])
  have hc3 : n {x,y,w} ≤ 1 := triple_trace_card_le_one F {x,y,z,w} {x,y,w} hR hu hf (by simp [Finset.insert_subset_iff]) (by simp [hxy,hxw,hyw])
  have hc4 : n {x,y,z} ≤ 1 := triple_trace_card_le_one F {x,y,z,w} {x,y,z} hR hu hf (by simp [Finset.insert_subset_iff]) (by simp [hxy,hxz,hyz])
  have hn : 53 ≤ n {x}+n {y}+n {z}+n {w}+n {x,y}+n {x,z}+n {x,w}+
      n {y,z}+n {y,w}+n {z,w}+n {y,z,w}+n {x,z,w}+n {x,y,w}+n {x,y,z}:= by
    clear * - hpart h0 h4 hc
    omega
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
  have hdx' : (F.filter (fun S => x ∈ S)).card = 1+n {x}+n {x,y}+n {x,z}+n {x,w}+n {x,z,w}+n {x,y,w}+n {x,y,z} := by
    clear * - hdx h4
    omega
  have hdy' : (F.filter (fun S => y ∈ S)).card = 1+n {y}+n {x,y}+n {y,z}+n {y,w}+n {y,z,w}+n {x,y,w}+n {x,y,z} := by
    clear * - hdy h4
    omega
  have hdz' : (F.filter (fun S => z ∈ S)).card = 1+n {z}+n {x,z}+n {y,z}+n {z,w}+n {y,z,w}+n {x,z,w}+n {x,y,z} := by
    clear * - hdz h4
    omega
  have hdw' : (F.filter (fun S => w ∈ S)).card = 1+n {w}+n {x,w}+n {y,w}+n {z,w}+n {y,z,w}+n {x,z,w}+n {x,y,w} := by
    clear * - hdw h4
    omega
  have hsx : n {x} ≤ 10 := singleton_trace_card_le_ten F {x,y,z,w} {x} hR hu hf (by simp)
  have hsy : n {y} ≤ 10 := singleton_trace_card_le_ten F {x,y,z,w} {y} hR hu hf (by simp)
  have hsz : n {z} ≤ 10 := singleton_trace_card_le_ten F {x,y,z,w} {z} hR hu hf (by simp)
  have hsw : n {w} ≤ 10 := singleton_trace_card_le_ten F {x,y,z,w} {w} hR hu hf (by simp)
  apply degree_cap_eighteen_trace_profile54 (n {x}) (n {y}) (n {z}) (n {w})
    (n {y,z,w}) (n {x,z,w}) (n {x,y,w}) (n {x,y,z})
    (degree F x) (degree F y) (degree F z) (degree F w)
    hsx hsy hsz hsw hc1 hc2 hc3 hc4
  · change (F.filter (fun S => x ∈ S)).card + 2 * n {x} + _ ≤ _
    clear * - hs1 hdx'
    omega
  · change (F.filter (fun S => y ∈ S)).card + 2 * n {y} + _ ≤ _
    clear * - hs2 hdy'
    omega
  · change (F.filter (fun S => z ∈ S)).card + 2 * n {z} + _ ≤ _
    clear * - hs3 hdz'
    omega
  · change (F.filter (fun S => w ∈ S)).card + 2 * n {w} + _ ≤ _
    clear * - hs4 hdw'
    omega
  · exact hd x
  · exact hd y
  · exact hd z
  · exact hd w
  · change _ ≤ (F.filter (fun S => x ∈ S)).card + (F.filter (fun S => y ∈ S)).card +
      (F.filter (fun S => z ∈ S)).card + (F.filter (fun S => w ∈ S)).card + _
    clear * - hdx' hdy' hdz' hdw' hn
    omega

/-- With all point degrees at most18, every singleton trace at a near-boundary
anchor has size at least9, and one reaches10. -/
theorem meeting_at_least_fifty_four_degree_cap_eighteen_traces
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card=4) (hf : IsSunflowerFree F 3)
    (hd : ∀ x, degree F x≤18)
    (R : Finset α) (hR : R ∈ F)
    (hc : 54 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card) :
    (∀ x ∈ R, 9 ≤ (exactTrace F R {x}).card) ∧
    ∃ x ∈ R, (exactTrace F R {x}).card=10 := by
  classical
  obtain ⟨x,y,z,w,hxy,hxz,hxw,hyz,hyw,hzw,hshape⟩ := Finset.card_eq_four.mp (hu R hR)
  subst R
  let N := F.filter (fun S => (S ∩ {x,y,z,w}).Nonempty)
  have hNF : N ⊆ F := Finset.filter_subset _ _
  have hRN : {x,y,z,w} ∈ N := Finset.mem_filter.mpr ⟨hR,by simp⟩
  have hNu : ∀ S ∈ N, S.card=4 := fun S hS => hu S (hNF hS)
  have hNf : IsSunflowerFree N 3 := fun H hH hs => hf H (hH.trans hNF) hs
  have hhit : ∀ S ∈ N, (S ∩ {x,y,z,w}).Nonempty := fun S hS => (Finset.mem_filter.mp hS).2
  have hNd : ∀ p, degree N p≤18 := by
    intro p
    exact (Finset.card_le_card (Finset.filter_subset_filter (fun S => p ∈ S) hNF)).trans (hd p)
  have hp := all_meeting_fifty_four_degree_cap_eighteen_traces N hNu hNf hc
    x y z w hxy hxz hxw hyz hyw hzw hRN hhit hNd
  have ht (p : α) : exactTrace N {x,y,z,w} {p} = exactTrace F {x,y,z,w} {p} := by
    ext S
    simp only [exactTrace,N,Finset.mem_filter]
    constructor
    · rintro ⟨⟨hSF,_⟩,hEq⟩
      exact ⟨hSF,hEq⟩
    · rintro ⟨hSF,hEq⟩
      refine ⟨⟨hSF,?_⟩,hEq⟩
      rw [hEq]
      simp
  rw [ht x,ht y,ht z,ht w] at hp
  obtain ⟨hsx,hsy,hsz,hsw,he⟩ := hp
  constructor
  · intro p hp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact hsx
    · exact hsy
    · exact hsz
    · exact hsw
  · rcases he with he | he | he | he
    · exact ⟨x,by simp,he⟩
    · exact ⟨y,by simp,he⟩
    · exact ⟨z,by simp,he⟩
    · exact ⟨w,by simp,he⟩

end Erdos20V10Profile54Bridge
