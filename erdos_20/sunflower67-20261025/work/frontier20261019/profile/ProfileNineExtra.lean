import ProfileNine
import SunflowerLean.Erdos20V9Census

namespace FrontierNine
open Erdos20BCWConditional Erdos20RankThree Erdos20TracePatterns
open Erdos20ExtremalStructure Erdos20DegreeCongruences Erdos20Incidence Erdos20V9Census

set_option maxHeartbeats 1500000

theorem triple_shape_at {α : Type*} [DecidableEq α]
    (R : Finset α) (hR : R.card=3) (x : α) (hx : x∈R) :
    ∃ a b, x≠a ∧ x≠b ∧ a≠b ∧ R={x,a,b} := by
  obtain ⟨a,b,c,hab,hac,hbc,hs⟩ := Finset.card_eq_three.mp hR
  rw [hs] at hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨b,c,hab,hac,hbc,hs⟩
  · exact ⟨a,c,hab.symm,hbc,hac,by rw [hs]; ext t; simp; tauto⟩
  · exact ⟨a,b,hac.symm,hbc.symm,hab,by rw [hs]; ext t; simp; tauto⟩

theorem nine_member_degree_five_cap {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S∈F, S.card=3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S∈F, ∀ T∈F, (S∩T).Nonempty) (hn : F.card=9)
    (R : Finset α) (hR : R∈F) : (R.filter (fun x => degree F x=5)).card≤2 := by
  classical
  obtain ⟨a,b,c,hab,hac,hbc,hs⟩ := Finset.card_eq_three.mp (hu R hR)
  subst R
  have h := (nine_member_ordered_ledger F hu hf hi hn a b c hab hac hbc hR).2.2.2.1
  by_cases ha5 : degree F a = 5 <;> by_cases hb5 : degree F b = 5 <;>
    by_cases hc5 : degree F c = 5 <;>
    simp [ha5,hb5,hc5,hab,hac,hbc] at h ⊢ <;> omega

theorem nine_degree_five_class_card_le_three {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S∈F, S.card=3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S∈F, ∀ T∈F, (S∩T).Nonempty) (hn : F.card=9) :
    (degreeClass F 5).card≤3 := by
  have h := degree_predicate_incidence_le F (fun n => n=5) 2
    (nine_member_degree_five_cap F hu hf hi hn)
  change (∑ x∈degreeClass F 5, degree F x)≤2*F.card at h
  rw [degreeClass_sum,hn] at h
  omega

theorem nine_supported_degree_ge_two {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S∈F, S.card=3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S∈F, ∀ T∈F, (S∩T).Nonempty) (hn : F.card=9)
    (x : α) (hx : x∈support F) : 2≤degree F x := by
  obtain ⟨R,hR,hxR⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨a,b,hxa,hxb,hab,hs⟩ := triple_shape_at R (hu R hR) x hxR
  have hR' : {x,a,b}∈F := by rw [← hs]; exact hR
  exact (nine_member_ordered_ledger F hu hf hi hn x a b hxa hxb hab hR').1.1

theorem nine_no_degree_two {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S∈F, S.card=3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S∈F, ∀ T∈F, (S∩T).Nonempty) (hn : F.card=9)
    (x : α) : degree F x≠2 := by
  classical
  intro hx2
  let G := F.filter (fun R => x∈R)
  have hG : G.card=2 := hx2
  obtain ⟨R,hRG⟩ := Finset.card_pos.mp (show 0<G.card by omega)
  obtain ⟨hRF,hxR⟩ := Finset.mem_filter.mp hRG
  have he : (G.erase R).card=1 := by rw [Finset.card_erase_of_mem hRG,hG]
  obtain ⟨T,hT⟩ := Finset.card_pos.mp (show 0<(G.erase R).card by omega)
  obtain ⟨hTR,hTG⟩ := Finset.mem_erase.mp hT
  obtain ⟨hTF,hxT⟩ := Finset.mem_filter.mp hTG
  obtain ⟨a,b,hxa,hxb,hab,hs⟩ := triple_shape_at R (hu R hRF) x hxR
  have hR' : {x,a,b}∈F := by rw [← hs]; exact hRF
  obtain ⟨ha5,hb5,hxb0,hxa0,hxone⟩ :=
    (nine_member_ordered_ledger F hu hf hi hn x a b hxa hxb hab hR').2.1 hx2
  have hTa : a∉T := by
    intro haT
    by_cases hbT : b∈T
    · have hsub : R⊆T := by rw [hs]; simp [Finset.insert_subset_iff,hxT,haT,hbT]
      exact hTR (Finset.eq_of_subset_of_card_le hsub (by rw [hu T hTF,hu R hRF])).symm
    · have htrace : T∩{x,a,b}={x,a} := by
        ext t
        simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
        aesop
      have hp := Finset.card_pos.mpr (show (exactTrace F {x,a,b} {x,a}).Nonempty from
        ⟨T,Finset.mem_filter.mpr ⟨hTF,htrace⟩⟩)
      omega
  have hTb : b∉T := by
    intro hbT
    have htrace : T∩{x,a,b}={x,b} := by
      ext t
      simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
      aesop
    have hp := Finset.card_pos.mpr (show (exactTrace F {x,a,b} {x,b}).Nonempty from
      ⟨T,Finset.mem_filter.mpr ⟨hTF,htrace⟩⟩)
    omega
  obtain ⟨c,d,hxc,hxd,hcd,hts⟩ := triple_shape_at T (hu T hTF) x hxT
  have hT' : {x,c,d}∈F := by rw [← hts]; exact hTF
  obtain ⟨hc5,hd5,_,_,_⟩ :=
    (nine_member_ordered_ledger F hu hf hi hn x c d hxc hxd hcd hT').2.1 hx2
  have hac : a≠c := fun h => hTa (by rw [hts,h]; simp)
  have had : a≠d := fun h => hTa (by rw [hts,h]; simp)
  have hbc : b≠c := fun h => hTb (by rw [hts,h]; simp)
  have hbd : b≠d := fun h => hTb (by rw [hts,h]; simp)
  have hsub : ({a,b,c,d} : Finset α)⊆degreeClass F 5 := by
    intro y hy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨member_subset_support hR' (by simp),ha5⟩
    · exact Finset.mem_filter.mpr ⟨member_subset_support hR' (by simp),hb5⟩
    · exact Finset.mem_filter.mpr ⟨member_subset_support hT' (by simp),hc5⟩
    · exact Finset.mem_filter.mpr ⟨member_subset_support hT' (by simp),hd5⟩
  have hcard : ({a,b,c,d} : Finset α).card=4 := by simp [hab,hac,had,hbc,hbd,hcd]
  have hle := Finset.card_le_card hsub
  have hcap := nine_degree_five_class_card_le_three F hu hf hi hn
  omega

theorem nine_supported_degree_ge_three {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S∈F, S.card=3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S∈F, ∀ T∈F, (S∩T).Nonempty) (hn : F.card=9)
    (x : α) (hx : x∈support F) : 3≤degree F x := by
  have h2 := nine_supported_degree_ge_two F hu hf hi hn x hx
  have hn2 := nine_no_degree_two F hu hf hi hn x
  omega

end FrontierNine
#print axioms FrontierNine.nine_member_degree_five_cap
#print axioms FrontierNine.nine_degree_five_class_card_le_three
#print axioms FrontierNine.nine_no_degree_two
#print axioms FrontierNine.nine_supported_degree_ge_three
