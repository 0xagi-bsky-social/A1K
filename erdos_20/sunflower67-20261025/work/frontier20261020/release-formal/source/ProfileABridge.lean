import ProfileACounts
import SunflowerLean.Erdos20V11HighSupport

namespace FrontierProfileABridge
open Erdos20BCWConditional Erdos20StrictCore Erdos20DegreeCongruences
open Erdos20V8Boundary Erdos20V9Census FrontierProfileACounts

private theorem omit_degree_split {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (x v : α) :
    degree (F.filter (fun R => x ∉ R)) v + (upperStar F {x,v}).card = degree F v := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := F.filter (fun R => v ∈ R)) (p := fun R => x ∈ R)
  have he1 : (F.filter (fun R => v ∈ R)).filter (fun R => x ∈ R) = upperStar F {x,v} := by
    ext R
    simp only [Finset.mem_filter, upperStar, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    tauto
  have he2 : (F.filter (fun R => v ∈ R)).filter (fun R => x ∉ R) =
      (F.filter (fun R => x ∉ R)).filter (fun R => v ∈ R) := by
    ext R
    simp only [Finset.mem_filter]
    tauto
  rw [he1,he2] at h
  simpa only [degree, Nat.add_comm] using h

theorem residual_profile_of_profile_a
    (hA : Erdos20V13Boundary.ProfileARealizable) :
    ∃ (α : Type) (_ : DecidableEq α), Nonempty (ResidualProfileA α) := by
  classical
  obtain ⟨α,inst,F,hu,hf,h81,h17,_,_,h19,hhigh,_⟩ := hA
  letI := inst
  obtain ⟨x,hxeq⟩ := Finset.card_eq_one.mp hhigh
  have hxhigh : x ∈ highPoints F := by rw [hxeq]; simp
  have hxS : x ∈ support F := (Finset.mem_filter.mp hxhigh).1
  have hx20 : degree F x = 20 := (Finset.mem_filter.mp hxhigh).2
  let U := support (residualLink F {x})
  let H := F.filter (fun R => x ∉ R)
  let O := support F \ insert x U
  have hL := Erdos20V11HighSupport.high_link_twenty_and_support_twelve F hu hf x hxhigh
  have hxU : x ∉ U := by
    intro hx
    obtain ⟨P,hP,hxP⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨R,hR,hxR,hRP⟩ := mem_residualLink_iff.mp hP
    rw [← hRP] at hxP
    exact (Finset.mem_sdiff.mp hxP).2 (by simp)
  have hUS : U ⊆ support F := by
    intro v hv
    obtain ⟨P,hP,hvP⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨R,hR,hxR,hRP⟩ := mem_residualLink_iff.mp hP
    rw [← hRP] at hvP
    exact member_subset_support hR (Finset.mem_sdiff.mp hvP).1
  have hlow : ∀ v ∈ support F, v ≠ x → degree F v = 19 := by
    have hsub : degreeClass F 19 ⊆ (support F).erase x := by
      intro v hv
      obtain ⟨hvS,hv19⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_erase.mpr ⟨by intro he; subst v; omega,hvS⟩
    have he : degreeClass F 19 = (support F).erase x :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_erase_of_mem hxS,h17,h19])
    intro v hv hvx
    have hv' : v ∈ degreeClass F 19 := by rw [he]; exact Finset.mem_erase.mpr ⟨hvx,hv⟩
    exact (Finset.mem_filter.mp hv').2
  have hH61 : H.card = 61 := by
    have hh := Finset.filter_card_add_filter_neg_card_eq_card (s := F) (p := fun R => x ∈ R)
    change degree F x + H.card = F.card at hh
    omega
  have hO4 : O.card = 4 := by
    have hh := Finset.card_sdiff_add_card_inter (support F) (insert x U)
    have hhsub : insert x U ⊆ support F := Finset.insert_subset hxS hUS
    rw [Finset.inter_eq_right.mpr hhsub,Finset.card_insert_of_notMem hxU] at hh
    change O.card + (U.card + 1) = (support F).card at hh
    have hU12 : U.card = 12 := hL.2
    omega
  have hpair : ∀ v, v ≠ x →
      (upperStar F {x,v}).card = if v ∈ U then 5 else 0 := by
    intro v hvx
    have heq : ((residualLink F {x}).filter (fun P => v ∈ P)).card =
        (upperStar F {x,v}).card := by
      simpa [Finset.pair_comm] using card_filter_residualLink F ({x} : Finset α) {v} (by simpa using hvx)
    rw [← heq]
    by_cases hvU : v ∈ U
    · simp only [hvU,if_pos]
      exact (Erdos20ExtremalTwenty.extremal_twenty_regular_twelve _
        (by simpa using residualLink_uniform (core := ({x} : Finset α)) hu)
        (residualLink_sunflowerFree hf) hL.1).2 v hvU
    · simp only [hvU,if_false]
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro P hP
      exact hvU (member_subset_support (Finset.mem_filter.mp hP).1 (Finset.mem_filter.mp hP).2)
  refine ⟨α, inst, ⟨{
    F := F
    H := H
    x := x
    O := O
    uniform := hu
    free := hf
    residual_subset := Finset.filter_subset _ _
    residual_card := hH61
    center_omitted := ?_
    link_card := hL.1
    outsiders_disjoint := ?_
    outsiders_card := hO4
    outside_degrees := ?_
    inside_degrees := ?_ }⟩⟩
  · intro R hR
    exact (Finset.mem_filter.mp hR).2
  · apply Finset.disjoint_left.mpr
    intro v hvO hvU
    exact (Finset.mem_sdiff.mp hvO).2 (Finset.mem_insert_of_mem hvU)
  · intro v hvO
    obtain ⟨hvS,hvN⟩ := Finset.mem_sdiff.mp hvO
    have hvx : v ≠ x := by intro he; subst v; exact hvN (Finset.mem_insert_self _ _)
    have hvU : v ∉ U := fun hv => hvN (Finset.mem_insert_of_mem hv)
    have hd := omit_degree_split F x v
    have hp := hpair v hvx
    rw [if_neg hvU] at hp
    have h19v := hlow v hvS hvx
    change degree H v + (upperStar F {x,v}).card = degree F v at hd
    omega
  · intro v hvO
    by_cases hvx : v = x
    · subst v
      have he : degree H x = 0 := by simp [degree,H,Finset.filter_filter]
      omega
    · by_cases hvS : v ∈ support F
      · have hvU : v ∈ U := by
          by_contra hn
          apply hvO
          exact Finset.mem_sdiff.mpr ⟨hvS,by simp only [Finset.mem_insert]; tauto⟩
        have hd := omit_degree_split F x v
        have hp := hpair v hvx
        rw [if_pos hvU] at hp
        have h19v := hlow v hvS hvx
        change degree H v + (upperStar F {x,v}).card = degree F v at hd
        omega
      · have he : degree H v = 0 := by
          apply Finset.card_eq_zero.mpr
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro R hR
          have hRH := (Finset.mem_filter.mp hR).1
          exact hvS (member_subset_support (Finset.mem_filter.mp hRH).1 (Finset.mem_filter.mp hR).2)
        omega

end FrontierProfileABridge
