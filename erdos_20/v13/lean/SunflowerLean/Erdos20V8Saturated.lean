import SunflowerLean.Erdos20V8Stability
import SunflowerLean.Erdos20RankFourRefined
namespace Erdos20V8Saturated
open Erdos20BCWConditional Erdos20RankThree Erdos20RankFour Erdos20RankFourRefined
open Erdos20V8Stability

/-- A saturated singleton trace in an intersecting rank-four family forces
at most twenty-six members. This is a restricted bound, not a universal upper26. -/
theorem ordered_saturated_singleton_card_le_twenty_six
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (x y z w : α) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) (hR : {x,y,z,w} ∈ F)
    (hsat : (exactTrace F {x,y,z,w} {x}).card = 10) : F.card ≤ 26 := by
  classical
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
  have hsum : n {x}+n {y}+n {z}+n {w} ≤ 20 :=
    rank_four_singleton_sum_le_twenty_of_ten F hu hf hi x y z w
      hxy hxz hxw hyz hyw hzw hR hsat
  have hsat' : n {x} = 10 := hsat
  have hz (C : Finset α) (q : α) (hqR : q ∈ ({x,y,z,w} : Finset α))
      (hxq : x ≠ q) (hxC : x ∈ C) (hqC : q ∉ C) (hC : C ≠ {x}) :
      n C = 0 ∨ n {q} = 0 :=
    saturated_trace_or_omitted_singleton_empty F {x,y,z,w} C hu hf hi hR x q
      (by simp) hqR hxq hsat hxC hqC hC
  have hzero0 := hz {x,y} z (by simp) hxz (by simp) (by simp [Ne.symm hxz,Ne.symm hyz]) (by intro he; have hc := congrArg Finset.card he; simp [hxy] at hc)
  have hzero1 := hz {x,y} w (by simp) hxw (by simp) (by simp [Ne.symm hxw,Ne.symm hyw]) (by intro he; have hc := congrArg Finset.card he; simp [hxy] at hc)
  have hzero2 := hz {x,z} y (by simp) hxy (by simp) (by simp [Ne.symm hxy,hyz]) (by intro he; have hc := congrArg Finset.card he; simp [hxz] at hc)
  have hzero3 := hz {x,z} w (by simp) hxw (by simp) (by simp [Ne.symm hxw,Ne.symm hzw]) (by intro he; have hc := congrArg Finset.card he; simp [hxz] at hc)
  have hzero4 := hz {x,w} y (by simp) hxy (by simp) (by simp [Ne.symm hxy,hyw]) (by intro he; have hc := congrArg Finset.card he; simp [hxw] at hc)
  have hzero5 := hz {x,w} z (by simp) hxz (by simp) (by simp [Ne.symm hxz,hzw]) (by intro he; have hc := congrArg Finset.card he; simp [hxw] at hc)
  have hzero6 := hz {x,z,w} y (by simp) hxy (by simp) (by simp [Ne.symm hxy,hyz,hyw]) (by intro he; have hc := congrArg Finset.card he; simp [hxz,hxw,hzw] at hc)
  have hzero7 := hz {x,y,w} z (by simp) hxz (by simp) (by simp [Ne.symm hxz,Ne.symm hyz,hzw]) (by intro he; have hc := congrArg Finset.card he; simp [hxy,hxw,hyw] at hc)
  have hzero8 := hz {x,y,z} w (by simp) hxw (by simp) (by simp [Ne.symm hxw,Ne.symm hyw,Ne.symm hzw]) (by intro he; have hc := congrArg Finset.card he; simp [hxy,hxz,hyz] at hc)
  clear * - hpart h0 h4 hp1 hp2 hp3 hb1 hb2 hb3 hb4 hb5 hb6 hc1 hc2 hc3 hc4 hsum hsat' hzero0 hzero1 hzero2 hzero3 hzero4 hzero5 hzero6 hzero7 hzero8
  omega

/-- The saturated-trace bound with an arbitrary ambient anchor. -/
theorem saturated_singleton_card_le_twenty_six
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (R : Finset α) (hR : R ∈ F) (x : α) (hx : x ∈ R)
    (hsat : (exactTrace F R {x}).card = 10) : F.card ≤ 26 := by
  have herase : (R.erase x).card = 3 := by rw [Finset.card_erase_of_mem hx,hu R hR]
  obtain ⟨y,z,w,hyz,hyw,hzw,he⟩ := Finset.card_eq_three.mp herase
  have hnot : x ∉ ({y,z,w} : Finset α) := he ▸ Finset.notMem_erase x R
  have hn : x ≠ y ∧ x ≠ z ∧ x ≠ w := by simpa using hnot
  have hshape : R = {x,y,z,w} := by rw [← he,Finset.insert_erase hx]
  subst R
  exact ordered_saturated_singleton_card_le_twenty_six F hu hf hi x y z w
    hn.1 hn.2.1 hn.2.2 hyz hyw hzw hR hsat

/-- Any intersecting family of at least27 has all singleton traces≤9. -/
theorem large_intersecting_singleton_trace_le_nine
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : 27 ≤ F.card)
    (R : Finset α) (hR : R ∈ F) (x : α) (hx : x ∈ R) :
    (exactTrace F R {x}).card ≤ 9 := by
  have hb := singleton_trace_card_le_ten F R {x} hR hu hf (by simp)
  by_contra hn
  have hs : (exactTrace F R {x}).card = 10 := by omega
  have hh := saturated_singleton_card_le_twenty_six F hu hf hi R hR x hx hs
  omega

end Erdos20V8Saturated
