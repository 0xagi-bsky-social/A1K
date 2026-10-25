import SunflowerLean.Erdos20V9HighCompatibility

namespace Erdos20V9HighCompatibility
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20ExtremalTwenty Erdos20DesignNormalForm Erdos20V8Boundary
open Erdos20DegreeCongruences Erdos20DesignCoordinates

/-- A member at a degree-twenty point has an isolated extremal component. -/
theorem high_point_component
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : degree F x = 20) (P : Finset α)
    (hP : P ∈ residualLink F {x}) :
    ∃ H ⊆ residualLink F {x}, P ∈ H ∧ H.card = 10 ∧
      (∀ A ∈ H, A.card = 3) ∧ IsSunflowerFree H 3 ∧
      (∀ A ∈ H, ∀ B ∈ H, (A ∩ B).Nonempty) ∧
      (∀ Q ∈ residualLink F {x}, (Q ∩ support H).Nonempty → Q ∈ H) := by
  have huL : ∀ A ∈ residualLink F {x}, A.card = 3 := by
    simpa using residualLink_uniform (core := ({x} : Finset α)) hu
  have hfL : IsSunflowerFree (residualLink F {x}) 3 := residualLink_sunflowerFree hf
  have hcL : (residualLink F {x}).card = 20 := by
    simpa [card_residualLink,upperStar,degree] using hx
  obtain ⟨H,hHL,hPH,hHc,hHi,hiso⟩ :=
    twenty_component_at_member (residualLink F {x}) huL hfL hcL P hP
  exact ⟨H,hHL,hPH,hHc,fun A hA => huL A (hHL hA),
    fun G hG hg => hfL G (hG.trans hHL) hg,hHi,hiso⟩

set_option maxHeartbeats 800000 in
/-- Three degree-twenty points cannot occur in a single rank-four member. -/
theorem no_three_high_in_four_member
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (x y z w : α)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (hR : {x,y,z,w} ∈ F)
    (hx : degree F x = 20) (hy : degree F y = 20) (hz : degree F z = 20) : False := by
  classical
  have hPx := triple_link_of_four_member F x y z w hxy hxz hxw hR
  obtain ⟨H,hHL,hPH,hHc,hHu,hHf,hHi,hisoH⟩ :=
    high_point_component F hu hf x hx {y,z,w} hPx
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc,hsH,hshapeH⟩ :=
    ten_anchor_normal_form H hHu hHf hHi hHc y z w hyz hyw hzw hPH
  have haY : a ≠ y := by intro he; subst a; simp at ha
  have haZ : a ≠ z := by intro he; subst a; simp at ha
  have haW : a ≠ w := by intro he; subst a; simp at ha
  have hbY : b ≠ y := by intro he; subst b; simp at hb
  have hbZ : b ≠ z := by intro he; subst b; simp at hb
  have hbW : b ≠ w := by intro he; subst b; simp at hb
  have hcY : c ≠ y := by intro he; subst c; simp at hc
  have hcZ : c ≠ z := by intro he; subst c; simp at hc
  have hcW : c ≠ w := by intro he; subst c; simp at hc
  have hZWA : {z,w,a} ∈ H := by rw [hshapeH]; simp [canonicalTen]
  have hYWB : {y,w,b} ∈ H := by rw [hshapeH]; simp [canonicalTen]
  have hYZC : {y,z,c} ∈ H := by rw [hshapeH]; simp [canonicalTen]
  have hYAB : {y,a,b} ∈ H := by rw [hshapeH]; simp [canonicalTen]
  have hYAC : {y,a,c} ∈ H := by rw [hshapeH]; simp [canonicalTen]
  have hxA : x ≠ a := by
    intro he
    have hn := point_not_mem_residue F x {z,w,a} (hHL hZWA)
    apply hn
    simp [he]
  have hxB : x ≠ b := by
    intro he
    have hn := point_not_mem_residue F x {y,w,b} (hHL hYWB)
    apply hn
    simp [he]
  have hxC : x ≠ c := by
    intro he
    have hn := point_not_mem_residue F x {y,z,c} (hHL hYZC)
    apply hn
    simp [he]
  have hPy : {x,z,w} ∈ residualLink F {y} :=
    switch_triple_link F x y z w hxy hyz hyw hPx
  obtain ⟨K,hKL,hPK,hKc,hKu,hKf,hKi,hisoK⟩ :=
    high_point_component F hu hf y hy {x,z,w} hPy
  have hxK : x ∈ support K := member_subset_support hPK (by simp)
  have hXWB : {x,w,b} ∈ K := by
    apply hisoK _ (switch_triple_link F x y w b hxy hyw hbY.symm (hHL hYWB))
    exact ⟨x,Finset.mem_inter.mpr ⟨by simp,hxK⟩⟩
  have hXZC : {x,z,c} ∈ K := by
    apply hisoK _ (switch_triple_link F x y z c hxy hyz hcY.symm (hHL hYZC))
    exact ⟨x,Finset.mem_inter.mpr ⟨by simp,hxK⟩⟩
  obtain ⟨u,huOut,huMem⟩ := ten_pair_has_outside_extension K hKu hKf hKi hKc
    {x,z,w} {z,w} hPK (by simp) (by simp [hzw])
  have hZWU : {z,w,u} ∈ K := by
    convert huMem using 1
    ext t
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  have hbKout : b ∉ ({x,z,w} : Finset α) := by simp [hxB.symm,hbZ,hbW]
  have hcKout : c ∉ ({x,z,w} : Finset α) := by simp [hxC.symm,hcZ,hcW]
  have hshapeK := ten_normal_form_of_extensions K hKu hKf hKi hKc
    x z w u b c hxz hxw hzw huOut hbKout hcKout hPK hZWU hXWB hXZC
  have hXUB : {x,u,b} ∈ K := by rw [hshapeK]; simp [canonicalTen]
  have huX : u ≠ x := by intro he; subst u; simp at huOut
  have huW : u ≠ w := by intro he; subst u; simp at huOut
  have hYUB : {y,u,b} ∈ H := by
    apply hisoH _ (switch_triple_link F y x u b hxy.symm huX.symm hxB (hKL hXUB))
    exact ⟨y,Finset.mem_inter.mpr ⟨by simp,member_subset_support hPH (by simp)⟩⟩
  have hneq : ({y,w,b} : Finset α) ≠ {y,a,b} := by
    intro he
    have hm : w ∈ ({y,a,b} : Finset α) := he ▸ (by simp : w ∈ ({y,w,b} : Finset α))
    simp [hyw.symm,haW.symm,hbW.symm] at hm
  have hpair := pair_star_eq_of_two H hHu hHf {y,w,b} {y,a,b} {y,b}
    hYWB hYAB hneq (by simp [Finset.insert_subset_iff]) (by simp [Finset.insert_subset_iff])
    (by simp [hbY.symm])
  have hUchoice : {y,u,b} ∈ H.filter (fun S => ({y,b} : Finset α) ⊆ S) :=
    Finset.mem_filter.mpr ⟨hYUB,by simp [Finset.insert_subset_iff]⟩
  rw [hpair] at hUchoice
  have hua : u = a := by
    rcases Finset.mem_insert.mp hUchoice with he | he
    · have hm : u ∈ ({y,w,b} : Finset α) := he ▸ (by simp : u ∈ ({y,u,b} : Finset α))
      have huB : u ≠ b := by
        intro heb
        have hcard := hHu {y,u,b} hYUB
        simp [heb,hbY.symm] at hcard
      have huY : u ≠ y := by
        intro hey
        have hcard := hHu {y,u,b} hYUB
        simp [hey,hbY.symm] at hcard
      simp [huY,huW,huB] at hm
    · have he := Finset.mem_singleton.mp he
      have hm : u ∈ ({y,a,b} : Finset α) := he ▸ (by simp : u ∈ ({y,u,b} : Finset α))
      have huB : u ≠ b := by
        intro heb
        have hcard := hHu {y,u,b} hYUB
        simp [heb,hbY.symm] at hcard
      have huY : u ≠ y := by
        intro hey
        have hcard := hHu {y,u,b} hYUB
        simp [hey,hbY.symm] at hcard
      simpa [huY,huB] using hm
  have hZWAk : {z,w,a} ∈ K := hua ▸ hZWU
  have hPz : {x,y,w} ∈ residualLink F {z} := by
    have hperm : ({z,y,w} : Finset α) = {y,z,w} := by ext t; simp [or_left_comm]
    exact switch_triple_link F x z y w hxz hyz.symm hzw (hperm ▸ hPx)
  obtain ⟨J,hJL,hPJ,hJc,hJu,hJf,hJi,hisoJ⟩ :=
    high_point_component F hu hf z hz {x,y,w} hPz
  have hwJ : w ∈ support J := member_subset_support hPJ (by simp)
  have hXWA : {x,w,a} ∈ J := by
    apply hisoJ _ (switch_triple_link F x z w a hxz hzw haZ.symm (hHL hZWA))
    exact ⟨w,Finset.mem_inter.mpr ⟨by simp,hwJ⟩⟩
  have hYWA : {y,w,a} ∈ J := by
    apply hisoJ _ (switch_triple_link F y z w a hyz hzw haZ.symm (hKL hZWAk))
    exact ⟨w,Finset.mem_inter.mpr ⟨by simp,hwJ⟩⟩
  apply ten_forbids_three_faces J hJu hJf hJi hJc w x y a
    hxw.symm hyw.symm haW.symm hxy hxA haY.symm
  · have he : ({w,x,y} : Finset α) = {x,y,w} := by
      rw [Finset.insert_comm w x,Finset.pair_comm w y]
    rw [he]
    exact hPJ
  · simpa only [Finset.insert_comm] using hXWA
  · simpa only [Finset.insert_comm] using hYWA

/-- Unconditionally, each rank-four member contains at most two points of degree twenty. -/
theorem member_high_points_card_le_two
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (R : Finset α) (hR : R ∈ F) : (R ∩ highPoints F).card ≤ 2 := by
  by_contra hn
  have hlarge : 2 < (R ∩ highPoints F).card := by omega
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ := Finset.two_lt_card_iff.mp hlarge
  have hxR := (Finset.mem_inter.mp hx).1
  have hyR := (Finset.mem_inter.mp hy).1
  have hzR := (Finset.mem_inter.mp hz).1
  have hx20 : degree F x = 20 := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).2).2
  have hy20 : degree F y = 20 := (Finset.mem_filter.mp (Finset.mem_inter.mp hy).2).2
  have hz20 : degree F z = 20 := (Finset.mem_filter.mp (Finset.mem_inter.mp hz).2).2
  have hsub : ({x,y,z} : Finset α) ⊆ R := by simp [Finset.insert_subset_iff,hxR,hyR,hzR]
  have hdiff : (R \ {x,y,z}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub,hu R hR]
    simp [hxy,hxz,hyz]
  obtain ⟨w,hw⟩ := Finset.card_eq_one.mp hdiff
  have hwm : w ∈ R \ {x,y,z} := by rw [hw]; simp
  have hwx : w ≠ x := by intro he; subst w; exact (Finset.mem_sdiff.mp hwm).2 (by simp)
  have hwy : w ≠ y := by intro he; subst w; exact (Finset.mem_sdiff.mp hwm).2 (by simp)
  have hwz : w ≠ z := by intro he; subst w; exact (Finset.mem_sdiff.mp hwm).2 (by simp)
  have hshape : R = {x,y,z,w} := by
    have he := Finset.union_sdiff_of_subset hsub
    rw [hw] at he
    rw [← he]
    ext t
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  exact no_three_high_in_four_member F hu hf x y z w hxy hxz hwx.symm hyz hwy.symm hwz.symm
    (hshape ▸ hR) hx20 hy20 hz20

end Erdos20V9HighCompatibility
