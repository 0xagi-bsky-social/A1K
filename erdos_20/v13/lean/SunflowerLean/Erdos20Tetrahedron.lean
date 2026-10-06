import SunflowerLean.Erdos20GraphEquality
import SunflowerLean.Erdos20SharpTriples

/-! Tetrahedron neighborhoods eliminate saturated triple obstructions. -/
namespace Erdos20Tetrahedron
open Erdos20GraphEquality Erdos20CrossBounds Erdos20RankThree
open Erdos20BCWConditional Erdos20StrictCore

/-- Removing a triangle from an extremal graph leaves a disjoint triangle. -/
theorem six_edges_triangle_complement
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 2) (hf : IsSunflowerFree F 3) (hc : F.card = 6)
    (x y z : α) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hsub : ({{x,y},{x,z},{y,z}} : Finset (Finset α)) ⊆ F) :
    ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      Disjoint ({a,b,c} : Finset α) {x,y,z} ∧
      ({{a,b},{a,c},{b,c}} : Finset (Finset α)) ⊆ F := by
  classical
  let G : Finset (Finset α) := {{x,y},{x,z},{y,z}}
  let H := F \ G
  have hHsub : H ⊆ F := Finset.sdiff_subset
  have huH : ∀ S ∈ H, S.card = 2 := fun S hS => hu S (hHsub hS)
  have hfH : IsSunflowerFree H 3 := fun J hJ hsun => hf J (hJ.trans hHsub) hsun
  have hcross : ∀ S ∈ H, S ∩ {x,y,z} = ∅ := by
    intro S hS
    obtain ⟨hSF,hSG⟩ := Finset.mem_sdiff.mp hS
    exact triangle_isolated F x y z hxy hxz hyz
      (rank_two_three_petals_degree_le_two F hu hf) hsub S hSF hSG
  have hHdis : H ⊆ F.filter (fun S => S ∩ {x,y} = ∅) := by
    intro S hS
    refine Finset.mem_filter.mpr ⟨hHsub hS,?_⟩
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hA : a ∈ S ∩ {x,y,z} := by
      obtain ⟨haS,haV⟩ := Finset.mem_inter.mp ha
      refine Finset.mem_inter.mpr ⟨haS,?_⟩
      simp only [Finset.mem_insert,Finset.mem_singleton] at haV ⊢
      tauto
    simpa [hcross S hS] using hA
  have hiH : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty := by
    intro S hS T hT
    exact disjoint_anchor_family_intersecting F {x,y} (hsub (by simp)) (by simp) hf
      S (hHdis hS) T (hHdis hT)
      (Finset.card_pos.mp (by rw [huH S hS]; decide))
      (Finset.card_pos.mp (by rw [huH T hT]; decide))
  have hHle := intersecting_rank_two_three_petals_card_le_three H huH hfH hiH
  have hGle : G.card ≤ 3 := by
    have h1 := Finset.card_insert_le ({x,y} : Finset α) ({{x,z},{y,z}} : Finset (Finset α))
    have h2 := Finset.card_insert_le ({x,z} : Finset α) ({{y,z}} : Finset (Finset α))
    simp only [Finset.card_singleton] at h2
    dsimp [G]
    omega
  have hcH : H.card = 3 := by
    have hs : H.card = F.card - G.card := Finset.card_sdiff_of_subset hsub
    omega
  obtain ⟨a,b,c,hab,hac,hbc,hH⟩ := intersecting_three_edges_triangle H huH
    (rank_two_three_petals_degree_le_two H huH hfH) hiH hcH
  have hout : ∀ t ∈ ({a,b,c} : Finset α), t ∉ ({x,y,z} : Finset α) := by
    intro t ht hin
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with he | he | he
    · have hi := hcross {a,b} (by simp [hH])
      have hm : a ∈ ({a,b} : Finset α) ∩ {x,y,z} := by simp [← he,hin]
      simpa [hi] using hm
    · have hi := hcross {a,b} (by simp [hH])
      have hm : b ∈ ({a,b} : Finset α) ∩ {x,y,z} := by simp [← he,hin]
      simpa [hi] using hm
    · have hi := hcross {a,c} (by simp [hH])
      have hm : c ∈ ({a,c} : Finset α) ∩ {x,y,z} := by simp [← he,hin]
      simpa [hi] using hm
  refine ⟨a,b,c,hab,hac,hbc,Finset.disjoint_left.mpr hout,?_⟩
  rw [← hH]
  exact hHsub

/-- The pairs of a three-point set are its three explicit edges. -/
theorem pair_subset_triangle_mem
    {α : Type*} [DecidableEq α] (a b c : α) (C : Finset α)
    (hC : C ∈ ({a,b,c} : Finset α).powersetCard 2) :
    C ∈ ({{a,b},{a,c},{b,c}} : Finset (Finset α)) := by
  obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp hC
  obtain ⟨p,q,hpq,rfl⟩ := Finset.card_eq_two.mp hcard
  have hp := hsub (by simp : p ∈ ({p,q} : Finset α))
  have hq := hsub (by simp : q ∈ ({p,q} : Finset α))
  simp only [Finset.mem_insert,Finset.mem_singleton] at hp hq
  rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq <;>
    subst p <;> subst q <;> simp_all [Finset.pair_comm]

/-- Deleting a distinguished point maps a triple to its opposite pair. -/
theorem triple_pair_in_link
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x y z : α)
    (hxy : x ≠ y) (hxz : x ≠ z) (hm : ({x,y,z} : Finset α) ∈ F) :
    ({y,z} : Finset α) ∈ residualLink F {x} := by
  apply mem_residualLink_iff.mpr
  refine ⟨{x,y,z},hm,by simp,?_⟩
  ext a
  simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton]
  grind

/-- A saturated point on a tetrahedron has a second link triangle entirely outside it. -/
theorem degree_six_outside_triangle
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x y z w : α)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxw : x ≠ w) (hyw : y ≠ w) (hzw : z ≠ w)
    (hxyz : ({x,y,z} : Finset α) ∈ F)
    (hxyw : ({x,y,w} : Finset α) ∈ F)
    (hxzw : ({x,z,w} : Finset α) ∈ F)
    (hxdeg : (F.filter (fun S => x ∈ S)).card = 6) :
    ∃ A : Finset α, A.card = 3 ∧ Disjoint A {x,y,z,w} ∧
      ∀ C ∈ A.powersetCard 2, insert x C ∈ F := by
  have hul : ∀ S ∈ residualLink F {x}, S.card = 2 := by
    simpa using residualLink_uniform (core := {x}) hu
  have hfl := residualLink_sunflowerFree (core := {x}) hf
  have hcl : (residualLink F {x}).card = 6 := by
    simpa [card_residualLink,upperStar] using hxdeg
  have hsub : ({{y,z},{y,w},{z,w}} : Finset (Finset α)) ⊆ residualLink F {x} := by
    intro C hC
    simp only [Finset.mem_insert,Finset.mem_singleton] at hC
    rcases hC with rfl | rfl | rfl
    · exact triple_pair_in_link F x y z hxy hxz hxyz
    · exact triple_pair_in_link F x y w hxy hxw hxyw
    · exact triple_pair_in_link F x z w hxz hxw hxzw
  obtain ⟨a,b,c,hab,hac,hbc,hdis,htri⟩ := six_edges_triangle_complement
    (residualLink F {x}) hul hfl hcl y z w hyz hyw hzw hsub
  have hax : a ≠ x := by
    have hd := residualLink_member_disjoint_core (htri (by simp : ({a,b} : Finset α) ∈ {{a,b},{a,c},{b,c}}))
    intro he
    exact Finset.disjoint_left.mp hd (by simp : x ∈ ({x} : Finset α)) (by simp [he])
  have hbx : b ≠ x := by
    have hd := residualLink_member_disjoint_core (htri (by simp : ({a,b} : Finset α) ∈ {{a,b},{a,c},{b,c}}))
    intro he
    exact Finset.disjoint_left.mp hd (by simp : x ∈ ({x} : Finset α)) (by simp [he])
  have hcx : c ≠ x := by
    have hd := residualLink_member_disjoint_core (htri (by simp : ({a,c} : Finset α) ∈ {{a,b},{a,c},{b,c}}))
    intro he
    exact Finset.disjoint_left.mp hd (by simp : x ∈ ({x} : Finset α)) (by simp [he])
  refine ⟨{a,b,c},by simp [hab,hac,hbc],?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro t ht htK
    rcases Finset.mem_insert.mp htK with he | htK
    · subst t
      simpa [Ne.symm hax,Ne.symm hbx,Ne.symm hcx] using ht
    · exact Finset.disjoint_left.mp hdis ht htK
  · intro C hC
    have hCL := htri (pair_subset_triangle_mem a b c C hC)
    have hm := core_union_residual_mem_family hCL
    have he : C ∪ {x} = insert x C := by ext t; simp
    simpa only [he] using hm

/-- A tetrahedron with a degree-six vertex has at most three members outside it. -/
theorem tetrahedron_disjoint_card_le_three
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x y z w : α)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxw : x ≠ w) (hyw : y ≠ w) (hzw : z ≠ w)
    (hxyz : ({x,y,z} : Finset α) ∈ F)
    (hxyw : ({x,y,w} : Finset α) ∈ F)
    (hxzw : ({x,z,w} : Finset α) ∈ F)
    (hyzw : ({y,z,w} : Finset α) ∈ F)
    (hxdeg : (F.filter (fun S => x ∈ S)).card = 6) :
    (F.filter (fun S => S ∩ {x,y,z,w} = ∅)).card ≤ 3 := by
  classical
  let K : Finset α := {x,y,z,w}
  let R : Finset α := {y,z,w}
  let D := F.filter (fun S => S ∩ K = ∅)
  obtain ⟨A,hA,hAK,hanch⟩ := degree_six_outside_triangle F x y z w hu hf
    hxy hxz hyz hxw hyw hzw hxyz hxyw hxzw hxdeg
  have hRK : R ⊆ K := by simp [R,K,Finset.insert_subset_iff]
  have hDx : ∀ S ∈ D, x ∉ S := by
    intro S hS hxS
    have he := (Finset.mem_filter.mp hS).2
    have hm : x ∈ S ∩ K := by simp [K,hxS]
    simpa [he] using hm
  have hDR : ∀ S ∈ D, S ∩ R = ∅ := by
    intro S hS
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hm : a ∈ S ∩ K := Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp ha).1,hRK (Finset.mem_inter.mp ha).2⟩
    simpa [(Finset.mem_filter.mp hS).2] using hm
  have hCR : ∀ C ∈ A.powersetCard 2, (insert x C) ∩ R = ∅ := by
    intro C hC
    have hCA := (Finset.mem_powersetCard.mp hC).1
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨haC,haR⟩ := Finset.mem_inter.mp ha
    rcases Finset.mem_insert.mp haC with he | haC
    · subst a
      simpa [R,hxy,hxz,hxw] using haR
    · exact Finset.disjoint_left.mp hAK (hCA haC) (hRK haR)
  have hhit : ∀ S ∈ D, ∀ C ∈ A.powersetCard 2, (S ∩ C).Nonempty := by
    intro S hS C hC
    have hsF := (Finset.mem_filter.mp hS).1
    have hcross := disjoint_anchor_family_intersecting F R hyzw (by simp [R]) hf
      S (Finset.mem_filter.mpr ⟨hsF,hDR S hS⟩)
      (insert x C) (Finset.mem_filter.mpr ⟨hanch C hC,hCR C hC⟩)
      (Finset.card_pos.mp (by rw [hu S hsF]; decide)) (by simp)
    obtain ⟨a,ha⟩ := hcross
    obtain ⟨haS,haC⟩ := Finset.mem_inter.mp ha
    rcases Finset.mem_insert.mp haC with he | haC
    · exact False.elim (hDx S hS (he ▸ haS))
    · exact ⟨a,Finset.mem_inter.mpr ⟨haS,haC⟩⟩
  apply Erdos20SharpTriples.triangle_pair_cover_card_le_three F D A hu hf
    (Finset.filter_subset _ _) hA
  · intro S hS
    exact Erdos20SharpTriples.contains_pair_of_meets_every_pair_of_triple A S hA (hhit S hS)
  · intro C hC
    refine ⟨insert x C,hanch C hC,?_,Finset.subset_insert _ _⟩
    intro hm
    exact hDx (insert x C) hm (by simp)

end Erdos20Tetrahedron
