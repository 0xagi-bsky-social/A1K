import SunflowerLean.Erdos20V9TraceBridge

namespace Erdos20V9ProfileBridge
open Erdos20BCWConditional Erdos20RankThree Erdos20RankFour Erdos20RankFourRefined
open Erdos20SaturatedMeeting Erdos20SharpTriples Erdos20V8Global
open Erdos20V9Profile Erdos20V8ProfileBridge Erdos20V8MeetingProfile Erdos20DegreeCongruences Erdos20V8Boundary

/-- Near-boundary meeting neighborhoods constrain the four actual point degrees. -/
theorem meeting_at_least_fifty_five_ordered_degree_pattern
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (x y z w : α) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) (hR : {x,y,z,w} ∈ F)
    (hc : 55 ≤ (F.filter (fun S => (S ∩ {x,y,z,w}).Nonempty)).card) :
    DegreePattern55 (degree F x) (degree F y) (degree F z) (degree F w) := by
  classical
  let N := F.filter (fun S => (S ∩ {x,y,z,w}).Nonempty)
  have hNF : N ⊆ F := Finset.filter_subset _ _
  have hRN : {x,y,z,w} ∈ N := Finset.mem_filter.mpr ⟨hR,by simp⟩
  have hNu : ∀ S ∈ N, S.card = 4 := fun S hS => hu S (hNF hS)
  have hNf : IsSunflowerFree N 3 := fun H hH hsun => hf H (hH.trans hNF) hsun
  have hhit : ∀ S ∈ N, (S ∩ {x,y,z,w}).Nonempty := fun S hS => (Finset.mem_filter.mp hS).2
  have hle : N.card ≤ 56 := Erdos20MeetingFiftySix.meeting_neighborhood_card_le_fifty_six F {x,y,z,w} hR hu hf
  have he : N.card = 55 ∨ N.card = 56 := by change 55 ≤ N.card at hc; omega
  have hp : DegreePattern55 (degree N x) (degree N y) (degree N z) (degree N w) := by
    rcases he with he | he
    · exact all_meeting_fifty_five_ordered_degree_pattern N hNu hNf he
        x y z w hxy hxz hxw hyz hyw hzw hRN hhit
    · have hp := all_meeting_fifty_six_ordered_degree_pattern N hNu hNf he
        x y z w hxy hxz hxw hyz hyw hzw hRN hhit
      unfold DegreePattern at hp
      unfold DegreePattern55
      omega
  dsimp only [N] at hp
  rw [degree_meeting_restriction_eq F {x,y,z,w} x (by simp),
      degree_meeting_restriction_eq F {x,y,z,w} y (by simp),
      degree_meeting_restriction_eq F {x,y,z,w} z (by simp),
      degree_meeting_restriction_eq F {x,y,z,w} w (by simp)] at hp
  exact hp

open Erdos20Incidence
/-- Degree16 and degree17 incidences have rigid companions at meeting size at least55. -/
theorem meeting_at_least_fifty_five_member_structure
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (R : Finset α) (hR : R ∈ F)
    (hc : 55 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card) :
    (∀ x ∈ R, 16 ≤ degree F x ∧ degree F x ≤ 20) ∧
    (∀ x ∈ R, degree F x = 16 → ∀ y ∈ R, y ≠ x → degree F y = 20) ∧
    (∀ x ∈ R, degree F x = 17 →
      (∀ y ∈ R, y ≠ x → 19 ≤ degree F y) ∧
      ∃ y ∈ R, degree F y = 20) ∧
    (R.filter (fun x => degree F x ≤ 18)).card ≤ 2 := by
  classical
  obtain ⟨x,y,z,w,hxy,hxz,hxw,hyz,hyw,hzw,hshape⟩ := Finset.card_eq_four.mp (hu R hR)
  subst R
  have hp := meeting_at_least_fifty_five_ordered_degree_pattern F hu hf
    x y z w hxy hxz hxw hyz hyw hzw hR hc
  rcases hp with ⟨hxa,hya,hza,hwa,hhi,hex,hey,hez,hew,hfx,hfy,hfz,hfw,hloABC,hloABD,hloACD,hloBCD⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro q hq
    simp only [Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hxa
    · exact hya
    · exact hza
    · exact hwa
  · intro p hp hd q hq hqp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl | rfl | rfl <;>
      rcases hq with rfl | rfl | rfl | rfl
    all_goals first | exact False.elim (hqp rfl) | omega
  · intro p hp hd
    constructor
    · intro q hq hqp
      simp only [Finset.mem_insert,Finset.mem_singleton] at hp hq
      rcases hp with rfl | rfl | rfl | rfl <;>
        rcases hq with rfl | rfl | rfl | rfl
      all_goals first | exact False.elim (hqp rfl) | omega
    · have hh : degree F x = 20 ∨ degree F y = 20 ∨ degree F z = 20 ∨ degree F w = 20 := by
        simp only [Finset.mem_insert,Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl | rfl <;> omega
      rcases hh with hh | hh | hh | hh
      · exact ⟨x,by simp,hh⟩
      · exact ⟨y,by simp,hh⟩
      · exact ⟨z,by simp,hh⟩
      · exact ⟨w,by simp,hh⟩

  · by_cases hx : degree F x ≤ 18 <;> by_cases hy : degree F y ≤ 18 <;>
      by_cases hz : degree F z ≤ 18 <;> by_cases hw : degree F w ≤ 18
    all_goals first | omega | (simp [Finset.filter_insert, Finset.filter_singleton, hx, hy, hz, hw, hxy, hxz, hxw, hyz, hyw, hzw] <;> omega)

/-- Under the degree-twenty cap, every supported point at the near boundary has degree at least17. -/
theorem all_meeting_at_least_fifty_five_degrees
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hm : ∀ R ∈ F, 55 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card)
    (hcap : ∀ R ∈ F, (R ∩ highPoints F).card ≤ 2) :
    ∀ x ∈ support F, 17 ≤ degree F x ∧ degree F x ≤ 20 := by
  classical
  intro x hx
  obtain ⟨R,hR,hxR⟩ := Finset.mem_biUnion.mp hx
  change x ∈ R at hxR
  have hp := meeting_at_least_fifty_five_member_structure F hu hf R hR (hm R hR)
  have hdx := hp.1 x hxR
  refine ⟨?_,hdx.2⟩
  by_contra hn
  have hx16 : degree F x = 16 := by omega
  have hsub : R.erase x ⊆ R ∩ highPoints F := by
    intro y hy
    obtain ⟨hyx,hyR⟩ := Finset.mem_erase.mp hy
    exact Finset.mem_inter.mpr ⟨hyR,Finset.mem_filter.mpr
      ⟨member_subset_support hR hyR,hp.2.1 x hxR hx16 y hyR hyx⟩⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hxR,hu R hR] at hc
  have hh := hcap R hR
  omega

/-- Low-degree point incidences are sparse in every near-boundary member. -/
theorem meeting_at_least_fifty_five_low_degree_caps
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (R : Finset α) (hR : R ∈ F)
    (hc : 55 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card) :
    (R.filter (fun x => degree F x = 17)).card ≤ 1 ∧
    (R.filter (fun x => degree F x ≤ 18)).card ≤ 2 := by
  classical
  have hp := meeting_at_least_fifty_five_member_structure F hu hf R hR hc
  refine ⟨?_,hp.2.2.2⟩
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hxR,hx17⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyR,hy17⟩ := Finset.mem_filter.mp hy
  by_contra hn
  have hh := (hp.2.2.1 x hxR hx17).1 y hyR (Ne.symm hn)
  omega

end Erdos20V9ProfileBridge
