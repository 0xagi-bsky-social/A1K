import SunflowerLean.Erdos20DesignCoordinates

/-! Coordinates of every intersecting extremal ten-triple family. -/
namespace Erdos20DesignNormalForm
open Erdos20BCWConditional Erdos20RankThree Erdos20V5Frontier Erdos20DesignCoordinates

/-- Three faces on four points with a common vertex cannot occur in an
intersecting extremal ten-triple family. -/
theorem ten_forbids_three_faces
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 10)
    (a b c q : α) (hab : a ≠ b) (hac : a ≠ c) (haq : a ≠ q)
    (hbc : b ≠ c) (hbq : b ≠ q) (hcq : c ≠ q)
    (hABC : {a,b,c} ∈ F) (hABQ : {a,b,q} ∈ F) (hACQ : {a,c,q} ∈ F) : False := by
  classical
  obtain ⟨hs,hd,_⟩ := intersecting_ten_design F hu hf hi hc
  have hbS : b ∈ support F := member_subset_support hABC (by simp)
  have hcS : c ∈ support F := member_subset_support hABC (by simp)
  have hqS : q ∈ support F := member_subset_support hABQ (by simp)
  have hneq1 : ({a,b,c} : Finset α) ≠ {a,b,q} := by
    intro he
    have hm : c ∈ ({a,b,q} : Finset α) := he ▸ (by simp : c ∈ ({a,b,c} : Finset α))
    simp [Ne.symm hac,Ne.symm hbc,hcq] at hm
  have hneq2 : ({a,b,c} : Finset α) ≠ {a,c,q} := by
    intro he
    have hm : b ∈ ({a,c,q} : Finset α) := he ▸ (by simp : b ∈ ({a,b,c} : Finset α))
    simp [Ne.symm hab,hbc,hbq] at hm
  have hneq3 : ({a,b,q} : Finset α) ≠ {a,c,q} := by
    intro he
    have hm : b ∈ ({a,c,q} : Finset α) := he ▸ (by simp : b ∈ ({a,b,q} : Finset α))
    simp [Ne.symm hab,hbc,hbq] at hm
  have hpab := pair_star_eq_of_two F hu hf {a,b,c} {a,b,q} {a,b}
    hABC hABQ hneq1 (by simp [Finset.insert_subset_iff]) (by simp [Finset.insert_subset_iff]) (by simp [hab])
  have hpac := pair_star_eq_of_two F hu hf {a,b,c} {a,c,q} {a,c}
    hABC hACQ hneq2 (by simp [Finset.insert_subset_iff]) (by simp [Finset.insert_subset_iff]) (by simp [hac])
  have hpaq := pair_star_eq_of_two F hu hf {a,b,q} {a,c,q} {a,q}
    hABQ hACQ hneq3 (by simp [Finset.insert_subset_iff]) (by simp [Finset.insert_subset_iff]) (by simp [haq])
  let D := support F \ {b,c,q}
  have hD : D.card = 3 := by
    rw [Finset.card_sdiff_of_subset (by simp [Finset.insert_subset_iff,hbS,hcS,hqS]),hs]
    simp [hbc,hbq,hcq]
  have hcover : F.filter (fun S => a ∈ S) ⊆ {{a,b,c},{a,b,q},{a,c,q},D} := by
    intro S hS
    obtain ⟨hSF,haS⟩ := Finset.mem_filter.mp hS
    by_cases hb : b ∈ S
    · have hm : S ∈ F.filter (fun S => ({a,b} : Finset α) ⊆ S) :=
        Finset.mem_filter.mpr ⟨hSF,by simp [Finset.insert_subset_iff,haS,hb]⟩
      rw [hpab] at hm
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm ⊢
      tauto
    by_cases hc : c ∈ S
    · have hm : S ∈ F.filter (fun S => ({a,c} : Finset α) ⊆ S) :=
        Finset.mem_filter.mpr ⟨hSF,by simp [Finset.insert_subset_iff,haS,hc]⟩
      rw [hpac] at hm
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm ⊢
      tauto
    by_cases hq : q ∈ S
    · have hm : S ∈ F.filter (fun S => ({a,q} : Finset α) ⊆ S) :=
        Finset.mem_filter.mpr ⟨hSF,by simp [Finset.insert_subset_iff,haS,hq]⟩
      rw [hpaq] at hm
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm ⊢
      tauto
    have hsub : S ⊆ D := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨member_subset_support hSF hx,by
        simp only [Finset.mem_insert,Finset.mem_singleton]
        rintro (rfl | rfl | rfl) <;> contradiction⟩
    have he : S = D := Finset.eq_of_subset_of_card_le hsub (by rw [hD,hu S hSF])
    simp [he]
  have hle := Finset.card_le_card hcover
  have hfour : ({{a,b,c},{a,b,q},{a,c,q},D} : Finset (Finset α)).card ≤ 4 :=
    Finset.card_le_four
  have haD := hd a (member_subset_support hABC (by simp))
  omega

/-- Each anchor pair has an extension by a point outside the anchor. -/
theorem ten_pair_has_outside_extension
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 10)
    (R C : Finset α) (hR : R ∈ F) (hCR : C ⊆ R) (hC : C.card = 2) :
    ∃ q : α, q ∉ R ∧ C ∪ {q} ∈ F := by
  classical
  have he := ten_pair_trace_card_one F hu hf hi hc R C hR hCR hC
  obtain ⟨S,hS⟩ := Finset.card_pos.mp (show 0 < (exactTrace F R C).card by omega)
  obtain ⟨hSF,hSR⟩ := Finset.mem_filter.mp hS
  have hCS : C ⊆ S := by rw [← hSR]; exact Finset.inter_subset_left
  have hr : (S \ C).card = 1 := by rw [Finset.card_sdiff_of_subset hCS,hu S hSF,hC]
  obtain ⟨q,hq⟩ := Finset.card_eq_one.mp hr
  have hqm : q ∈ S \ C := by rw [hq]; simp
  have hqR : q ∉ R := by
    intro hm
    apply (Finset.mem_sdiff.mp hqm).2
    rw [← hSR]
    exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hqm).1,hm⟩
  refine ⟨q,hqR,?_⟩
  have hshape : C ∪ {q} = S := by rw [← hq]; exact Finset.union_sdiff_of_subset hCS
  rw [hshape]
  exact hSF

/-- Extensions of two different anchor pairs use different outside points. -/
theorem ten_distinct_outside_extension_pair
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 10)
    (a b c q r : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hq : q ∉ ({a,b,c} : Finset α)) (hr : r ∉ ({a,b,c} : Finset α))
    (hABC : {a,b,c} ∈ F) (hABQ : {a,b,q} ∈ F) (hACR : {a,c,r} ∈ F) : q ≠ r := by
  intro he
  subst r
  have haq : a ≠ q := by intro he; subst q; simp at hq
  have hbq : b ≠ q := by intro he; subst q; simp at hq
  have hcq : c ≠ q := by intro he; subst q; simp at hq
  exact ten_forbids_three_faces F hu hf hi hc a b c q hab hac haq hbc hbq hcq hABC hABQ hACR

/-- The three outside extensions attached to an anchor are pairwise distinct. -/
theorem distinct_outside_extensions
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 10)
    (a b c za zb zc : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hza : za ∉ ({a,b,c} : Finset α)) (hzb : zb ∉ ({a,b,c} : Finset α))
    (hzc : zc ∉ ({a,b,c} : Finset α))
    (hABC : {a,b,c} ∈ F) (hBCA : {b,c,za} ∈ F)
    (hACB : {a,c,zb} ∈ F) (hABC' : {a,b,zc} ∈ F) :
    za ≠ zb ∧ za ≠ zc ∧ zb ≠ zc := by
  have hp1 : ({c,b,a} : Finset α) = {a,b,c} := by
    ext x; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
  have hp2 : ({b,c,a} : Finset α) = {a,b,c} := by
    ext x; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
  have hp3 : ({a,c,b} : Finset α) = {a,b,c} := by
    ext x; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
  constructor
  · apply ten_distinct_outside_extension_pair F hu hf hi hc c b a za zb
      (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab)
    · simpa only [hp1] using hza
    · simpa only [hp1] using hzb
    · simpa only [hp1] using hABC
    · simpa only [Finset.insert_comm] using hBCA
    · simpa only [Finset.insert_comm] using hACB
  constructor
  · apply ten_distinct_outside_extension_pair F hu hf hi hc b c a za zc
      hbc (Ne.symm hab) (Ne.symm hac)
    · simpa only [hp2] using hza
    · simpa only [hp2] using hzc
    · simpa only [hp2] using hABC
    · exact hBCA
    · simpa only [Finset.insert_comm] using hABC'
  · apply ten_distinct_outside_extension_pair F hu hf hi hc a c b zb zc
      hac hab (Ne.symm hbc)
    · simpa only [hp3] using hzb
    · simpa only [hp3] using hzc
    · simpa only [hp3] using hABC
    · exact hACB
    · exact hABC'

/-- Two distinct pairs of a triple cannot share the same outside extension. -/
theorem ten_forbids_common_outside_extension
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 10)
    (A : Finset α) (hA : A ∈ F) (m n : α) (hm : m ∈ A) (hn : n ∈ A)
    (hmn : m ≠ n) (z : α) (hz : z ∉ A)
    (hExtM : insert z (A.erase m) ∈ F) (hExtN : insert z (A.erase n) ∈ F) : False := by
  classical
  have hpair : ({m,n} : Finset α) ⊆ A := by simp [Finset.insert_subset_iff,hm,hn]
  have hcard : (A \ {m,n}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hpair,hu A hA]
    simp [hmn]
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hcard
  have ham : a ∈ A \ {m,n} := by rw [ha]; simp
  have ham' : a ≠ m := by
    intro he; subst a
    exact (Finset.mem_sdiff.mp ham).2 (by simp)
  have han' : a ≠ n := by
    intro he; subst a
    exact (Finset.mem_sdiff.mp ham).2 (by simp)
  have hshape : A = {a,m,n} := by
    have he := Finset.union_sdiff_of_subset hpair
    rw [ha] at he
    rw [← he]
    ext x
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  have heM : insert z (A.erase m) = {a,n,z} := by
    rw [hshape]
    ext x
    simp only [Finset.mem_insert,Finset.mem_erase,Finset.mem_singleton]
    constructor
    · rintro (rfl | ⟨hxm,rfl | rfl | rfl⟩) <;> simp_all
    · rintro (rfl | rfl | rfl) <;> simp_all [Ne.symm hmn]
  have heN : insert z (A.erase n) = {a,m,z} := by
    rw [hshape]
    ext x
    simp only [Finset.mem_insert,Finset.mem_erase,Finset.mem_singleton]
    constructor
    · rintro (rfl | ⟨hxn,rfl | rfl | rfl⟩) <;> simp_all
    · rintro (rfl | rfl | rfl) <;> simp_all [Ne.symm hmn]
  have haz : a ≠ z := by intro he; subst z; exact hz (Finset.mem_sdiff.mp ham).1
  have hmz : m ≠ z := by intro he; subst z; exact hz hm
  have hnz : n ≠ z := by intro he; subst z; exact hz hn
  exact ten_forbids_three_faces F hu hf hi hc a m n z ham' han' haz hmn hmz hnz
    (hshape ▸ hA) (heN ▸ hExtN) (heM ▸ hExtM)

/-- The support consists of the anchor and its three distinct outside extensions. -/
theorem six_point_support_of_extensions
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 10)
    (a b c za zb zc : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hza : za ∉ ({a,b,c} : Finset α)) (hzb : zb ∉ ({a,b,c} : Finset α))
    (hzc : zc ∉ ({a,b,c} : Finset α))
    (hABC : {a,b,c} ∈ F) (hBCA : {b,c,za} ∈ F)
    (hACB : {a,c,zb} ∈ F) (hABC' : {a,b,zc} ∈ F) :
    support F = {a,b,c,za,zb,zc} := by
  classical
  have hd := distinct_outside_extensions F hu hf hi hc a b c za zb zc hab hac hbc
    hza hzb hzc hABC hBCA hACB hABC'
  have hsub : ({a,b,c,za,zb,zc} : Finset α) ⊆ support F := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact member_subset_support hABC (by simp)
    · exact member_subset_support hABC (by simp)
    · exact member_subset_support hABC (by simp)
    · exact member_subset_support hBCA (by simp)
    · exact member_subset_support hACB (by simp)
    · exact member_subset_support hABC' (by simp)
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le hsub
  have hs := (intersecting_ten_design F hu hf hi hc).1
  rw [hs]
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hza hzb hzc
  simp_all [Finset.card_insert_of_notMem,ne_eq,eq_comm]

/-- A triple containing two specified distinct points and contained in four points
has one of the two expected forms. -/
theorem triple_of_two_mem_subset_four
    {α : Type*} [DecidableEq α] (S : Finset α) (a z u v : α)
    (hcard : S.card = 3) (haz : a ≠ z) (ha : a ∈ S) (hz : z ∈ S)
    (hsub : S ⊆ {a,z,u,v}) : S = {a,z,u} ∨ S = {a,z,v} := by
  have hp : ({a,z} : Finset α) ⊆ S := by simp [Finset.insert_subset_iff,ha,hz]
  have hdiff : (S \ {a,z}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hp,hcard]
    simp [haz]
  obtain ⟨w,hw⟩ := Finset.card_eq_one.mp hdiff
  have hwm : w ∈ S \ {a,z} := by rw [hw]; simp
  have hwu : w = u ∨ w = v := by
    have hm := hsub (Finset.mem_sdiff.mp hwm).1
    have hn := (Finset.mem_sdiff.mp hwm).2
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm hn
    tauto
  have hshape : S = {a,z,w} := by
    have he := Finset.union_sdiff_of_subset hp
    rw [hw] at he
    rw [← he]
    ext x; simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]; tauto
  rcases hwu with rfl | rfl
  · exact Or.inl hshape
  · exact Or.inr hshape

/-- The singleton trace at an anchor point has one of two canonical forms. -/
theorem singleton_member_shape
    {α : Type*} [DecidableEq α] (S : Finset α) (a b c za zb zc : α)
    (hcard : S.card = 3) (haza : a ≠ za) (ha : a ∈ S)
    (hb : b ∉ S) (hc : c ∉ S) (hsub : S ⊆ {a,b,c,za,zb,zc})
    (hmeet : (S ∩ {b,c,za}).Nonempty) :
    S = {a,za,zb} ∨ S = {a,za,zc} := by
  have hza : za ∈ S := by
    obtain ⟨x,hx⟩ := hmeet
    obtain ⟨hxS,hxB⟩ := Finset.mem_inter.mp hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hxB
    rcases hxB with rfl | rfl | rfl
    · exact False.elim (hb hxS)
    · exact False.elim (hc hxS)
    · exact hxS
  apply triple_of_two_mem_subset_four S a za zb zc hcard haza ha hza
  intro x hx
  have hm := hsub hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm ⊢
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · tauto
  · exact False.elim (hb hx)
  · exact False.elim (hc hx)
  · tauto
  · tauto
  · tauto

/-- A coordinate presentation of the unique intersecting ten-triple design. -/
def canonicalTen {α : Type*} [DecidableEq α] (a b c za zb zc : α) : Finset (Finset α) :=
  {{a,b,c}, {b,c,za}, {a,c,zb}, {a,b,zc},
   {a,za,zb}, {a,za,zc}, {b,zb,za}, {b,zb,zc}, {c,zc,za}, {c,zc,zb}}


/-- The displayed normal form has at most ten members, without distinctness assumptions. -/
theorem canonicalTen_card_le {α : Type*} [DecidableEq α] (a b c za zb zc : α) :
    (canonicalTen a b c za zb zc).card ≤ 10 := by
  unfold canonicalTen
  exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ
    ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ
    ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ
    ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ Finset.card_le_six)))))))

set_option maxHeartbeats 800000 in
/-- The anchor and its pair extensions determine every member of the design. -/
theorem ten_normal_form_of_extensions
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 10)
    (a b c za zb zc : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hza : za ∉ ({a,b,c} : Finset α)) (hzb : zb ∉ ({a,b,c} : Finset α))
    (hzc : zc ∉ ({a,b,c} : Finset α))
    (hABC : {a,b,c} ∈ F) (hBCA : {b,c,za} ∈ F)
    (hACB : {a,c,zb} ∈ F) (hABC' : {a,b,zc} ∈ F) :
    F = canonicalTen a b c za zb zc := by
  classical
  have hs := six_point_support_of_extensions F hu hf hi hc a b c za zb zc hab hac hbc
    hza hzb hzc hABC hBCA hACB hABC'
  have hneqA : ({a,b,c} : Finset α) ≠ {b,c,za} := by
    intro he; apply hza; rw [he]; simp
  have hneqB : ({a,b,c} : Finset α) ≠ {a,c,zb} := by
    intro he; apply hzb; rw [he]; simp
  have hneqC : ({a,b,c} : Finset α) ≠ {a,b,zc} := by
    intro he; apply hzc; rw [he]; simp
  have hpAB := pair_star_eq_of_two F hu hf {a,b,c} {a,b,zc} {a,b}
    hABC hABC' hneqC (by simp [Finset.insert_subset_iff])
    (by simp [Finset.insert_subset_iff]) (by simp [hab])
  have hpAC := pair_star_eq_of_two F hu hf {a,b,c} {a,c,zb} {a,c}
    hABC hACB hneqB (by simp [Finset.insert_subset_iff])
    (by simp [Finset.insert_subset_iff]) (by simp [hac])
  have hpBC := pair_star_eq_of_two F hu hf {a,b,c} {b,c,za} {b,c}
    hABC hBCA hneqA (by simp)
    (by simp [Finset.insert_subset_iff]) (by simp [hbc])
  have hsub : F ⊆ canonicalTen a b c za zb zc := by
    intro S hS
    simp only [canonicalTen,Finset.mem_insert,Finset.mem_singleton]
    by_cases habS : a ∈ S ∧ b ∈ S
    · have hm : S ∈ F.filter (fun S => ({a,b} : Finset α) ⊆ S) :=
        Finset.mem_filter.mpr ⟨hS,by simp [Finset.insert_subset_iff,habS.1,habS.2]⟩
      rw [hpAB] at hm
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      rcases hm with rfl | rfl <;> simp
    by_cases hacS : a ∈ S ∧ c ∈ S
    · have hm : S ∈ F.filter (fun S => ({a,c} : Finset α) ⊆ S) :=
        Finset.mem_filter.mpr ⟨hS,by simp [Finset.insert_subset_iff,hacS.1,hacS.2]⟩
      rw [hpAC] at hm
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      rcases hm with rfl | rfl <;> simp
    by_cases hbcS : b ∈ S ∧ c ∈ S
    · have hm : S ∈ F.filter (fun S => ({b,c} : Finset α) ⊆ S) :=
        Finset.mem_filter.mpr ⟨hS,by simp [Finset.insert_subset_iff,hbcS.1,hbcS.2]⟩
      rw [hpBC] at hm
      simp only [Finset.mem_insert,Finset.mem_singleton] at hm
      rcases hm with rfl | rfl <;> simp
    have hsubS : S ⊆ {a,b,c,za,zb,zc} := by
      rw [← hs]; exact member_subset_support hS
    have hmeet : a ∈ S ∨ b ∈ S ∨ c ∈ S := by
      obtain ⟨x,hx⟩ := hi S hS _ hABC
      obtain ⟨hxS,hxR⟩ := Finset.mem_inter.mp hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hxR
      rcases hxR with rfl | rfl | rfl
      · exact Or.inl hxS
      · exact Or.inr (Or.inl hxS)
      · exact Or.inr (Or.inr hxS)
    rcases hmeet with haS | hbS | hcS
    · have hbS : b ∉ S := fun hb => habS ⟨haS,hb⟩
      have hcS : c ∉ S := fun hc => hacS ⟨haS,hc⟩
      have haza : a ≠ za := by intro he; subst za; simp at hza
      have hh := singleton_member_shape S a b c za zb zc (hu S hS) haza haS hbS hcS
        hsubS (hi S hS _ hBCA)
      rcases hh with rfl | rfl <;> simp
    · have haS : a ∉ S := fun ha => habS ⟨ha,hbS⟩
      have hcS : c ∉ S := fun hc => hbcS ⟨hbS,hc⟩
      have hbzb : b ≠ zb := by intro he; subst zb; simp at hzb
      have hperm : ({b,a,c,zb,za,zc} : Finset α) = {a,b,c,za,zb,zc} := by
        ext x; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
      have hsubB : S ⊆ {b,a,c,zb,za,zc} := by rw [hperm]; exact hsubS
      have hh := singleton_member_shape S b a c zb za zc (hu S hS) hbzb hbS haS hcS
        hsubB (hi S hS _ hACB)
      rcases hh with rfl | rfl <;> simp
    · have haS : a ∉ S := fun ha => hacS ⟨ha,hcS⟩
      have hbS : b ∉ S := fun hb => hbcS ⟨hb,hcS⟩
      have hczc : c ≠ zc := by intro he; subst zc; simp at hzc
      have hperm : ({c,a,b,zc,za,zb} : Finset α) = {a,b,c,za,zb,zc} := by
        ext x; simp only [Finset.mem_insert,Finset.mem_singleton]; tauto
      have hsubC : S ⊆ {c,a,b,zc,za,zb} := by rw [hperm]; exact hsubS
      have hh := singleton_member_shape S c a b zc za zb (hu S hS) hczc hcS haS hbS
        hsubC (hi S hS _ hABC')
      rcases hh with rfl | rfl <;> simp
  apply Finset.eq_of_subset_of_card_le hsub
  rw [hc]
  exact canonicalTen_card_le a b c za zb zc

/-- Every intersecting ten-triple family has the same six-point normal form
relative to any ordering of any member. -/
theorem ten_anchor_normal_form
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 10)
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hABC : {a,b,c} ∈ F) :
    ∃ za zb zc : α,
      za ∉ ({a,b,c} : Finset α) ∧ zb ∉ ({a,b,c} : Finset α) ∧
      zc ∉ ({a,b,c} : Finset α) ∧ za ≠ zb ∧ za ≠ zc ∧ zb ≠ zc ∧
      support F = {a,b,c,za,zb,zc} ∧ F = canonicalTen a b c za zb zc := by
  obtain ⟨za,hza,hBa⟩ := ten_pair_has_outside_extension F hu hf hi hc {a,b,c} {b,c}
    hABC (by simp) (by simp [hbc])
  obtain ⟨zb,hzb,hBb⟩ := ten_pair_has_outside_extension F hu hf hi hc {a,b,c} {a,c}
    hABC (by simp [Finset.insert_subset_iff]) (by simp [hac])
  obtain ⟨zc,hzc,hBc⟩ := ten_pair_has_outside_extension F hu hf hi hc {a,b,c} {a,b}
    hABC (by simp [Finset.insert_subset_iff]) (by simp [hab])
  have hBCA : {b,c,za} ∈ F := by
    convert hBa using 1; ext x
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  have hACB : {a,c,zb} ∈ F := by
    convert hBb using 1; ext x
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  have hABC' : {a,b,zc} ∈ F := by
    convert hBc using 1; ext x
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  obtain ⟨habz,hacz,hbcz⟩ := distinct_outside_extensions F hu hf hi hc a b c za zb zc
    hab hac hbc hza hzb hzc hABC hBCA hACB hABC'
  refine ⟨za,zb,zc,hza,hzb,hzc,habz,hacz,hbcz,?_,?_⟩
  · exact six_point_support_of_extensions F hu hf hi hc a b c za zb zc
      hab hac hbc hza hzb hzc hABC hBCA hACB hABC'
  · exact ten_normal_form_of_extensions F hu hf hi hc a b c za zb zc
      hab hac hbc hza hzb hzc hABC hBCA hACB hABC'

/-- An anchor-free existence statement for the complete normal form. -/
theorem ten_has_normal_form
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 10) :
    ∃ a b c za zb zc : α,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      za ∉ ({a,b,c} : Finset α) ∧ zb ∉ ({a,b,c} : Finset α) ∧
      zc ∉ ({a,b,c} : Finset α) ∧ za ≠ zb ∧ za ≠ zc ∧ zb ≠ zc ∧
      support F = {a,b,c,za,zb,zc} ∧ F = canonicalTen a b c za zb zc := by
  obtain ⟨R,hR⟩ := Finset.card_pos.mp (show 0 < F.card by omega)
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp (hu R hR)
  obtain ⟨za,zb,zc,h⟩ := ten_anchor_normal_form F hu hf hi hc a b c hab hac hbc hR
  exact ⟨a,b,c,za,zb,zc,hab,hac,hbc,h⟩

set_option maxHeartbeats 800000 in
/-- Every extremal intersecting triple family is an injective relabeling of one
fixed family on `Fin 6`. This is the explicit uniqueness-up-to-relabeling theorem. -/
theorem ten_isomorphic_canonical
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 10) :
    ∃ e : Fin 6 ↪ α,
      F = (canonicalTen (0 : Fin 6) 1 2 3 4 5).image (fun S => S.image e) := by
  obtain ⟨a,b,c,za,zb,zc,hab,hac,hbc,hza,hzb,hzc,habz,hacz,hbcz,hs,hshape⟩ :=
    ten_has_normal_form F hu hf hi hc
  let f : Fin 6 → α := fun i =>
    if i = 0 then a else if i = 1 then b else if i = 2 then c else
    if i = 3 then za else if i = 4 then zb else zc
  have hinj : Function.Injective f := by
    clear hu hf hi hc hs hshape
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hza hzb hzc
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f,eq_comm]
  refine ⟨⟨f,hinj⟩,?_⟩
  rw [hshape]
  simp [canonicalTen,f]

end Erdos20DesignNormalForm
