import SunflowerLean.Erdos20V8Intersecting
import SunflowerLean.Erdos20ThreeCrossEdges

/-! Rigidity of saturated triangle constraints on triple families. -/
namespace Erdos20V9IntersectingTriangles
open Erdos20BCWConditional Erdos20RankThree Erdos20RankFour Erdos20RankFourRefined
open Erdos20MixedCross Erdos20SharpTriples Erdos20CrossBounds Erdos20GraphEquality Erdos20ThreeCrossEdges

/-- Meeting all pairs of a triple requires two of its points. -/
theorem two_points_of_meets_pairs
    {α : Type*} [DecidableEq α] (C S : Finset α) (hC : C.card = 3)
    (hh : ∀ P ∈ C.powersetCard 2, (S ∩ P).Nonempty) : 2 ≤ (S ∩ C).card := by
  obtain ⟨P,hP,hPS⟩ := contains_pair_of_meets_every_pair_of_triple C S hC hh
  obtain ⟨hPC,hP2⟩ := Finset.mem_powersetCard.mp hP
  simpa [hP2] using Finset.card_le_card (Finset.subset_inter hPS hPC)

/-- Two two-point intersections inside a triple have a common point. -/
theorem intersections_have_common_point
    {α : Type*} [DecidableEq α] (S C D : Finset α) (hS : S.card = 3)
    (hC : 2 ≤ (S ∩ C).card) (hD : 2 ≤ (S ∩ D).card) :
    (S ∩ (C ∩ D)).Nonempty := by
  have he := Finset.card_union_add_card_inter (S ∩ C) (S ∩ D)
  have hu : ((S ∩ C) ∪ (S ∩ D)).card ≤ 3 :=
    (Finset.card_le_card (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)).trans_eq hS
  have hi : (S ∩ C) ∩ (S ∩ D) = S ∩ (C ∩ D) := by ext x; simp [and_left_comm]
  rw [hi] at he
  exact Finset.card_pos.mp (by omega)

/-- For two triangles sharing an edge, all crossing triples either contain
that edge or are one of two exceptional triples. -/
theorem shared_edge_triangles_card_le_four
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (a b c d : α) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hh : ∀ S ∈ F,
      (S ∩ {a,b}).Nonempty ∧ (S ∩ {a,c}).Nonempty ∧ (S ∩ {b,c}).Nonempty ∧
      (S ∩ {a,d}).Nonempty ∧ (S ∩ {b,d}).Nonempty) : F.card ≤ 4 := by
  classical
  let A := F.filter (fun S => {a,b} ⊆ S)
  have hA : A.card ≤ 2 := triple_pair_degree_le_two F hu hf {a,b} (by simp [hab])
  have hcover : F ⊆ A ∪ {{a,c,d},{b,c,d}} := by
    intro S hS
    by_cases hpair : ({a,b} : Finset α) ⊆ S
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hS,hpair⟩)
    · apply Finset.mem_union_right
      obtain ⟨v,hv⟩ := (hh S hS).1
      have hav : a ∈ S ∨ b ∈ S := by
        obtain ⟨hvS,hvp⟩ := Finset.mem_inter.mp hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hvp
        rcases hvp with rfl | rfl
        · exact Or.inl hvS
        · exact Or.inr hvS
      have forced (u v : α) (hv : v ∉ S) (hmeet : (S ∩ {v,u}).Nonempty) : u ∈ S := by
        obtain ⟨z,hz⟩ := hmeet
        obtain ⟨hzS,hzp⟩ := Finset.mem_inter.mp hz
        simp only [Finset.mem_insert,Finset.mem_singleton] at hzp
        rcases hzp with rfl | rfl
        · exact False.elim (hv hzS)
        · exact hzS
      rcases hav with haS | hbS
      · have hbS : b ∉ S := fun hbS => hpair (by simp [Finset.insert_subset_iff,haS,hbS])
        have hcS := forced c b hbS (hh S hS).2.2.1
        have hdS := forced d b hbS (hh S hS).2.2.2.2
        have he : ({a,c,d} : Finset α) = S := Finset.eq_of_subset_of_card_le
          (by simp [Finset.insert_subset_iff,haS,hcS,hdS]) (by simp [hu S hS,hac,had,hcd])
        simp [← he]
      · have haS : a ∉ S := fun haS => hpair (by simp [Finset.insert_subset_iff,haS,hbS])
        have hcS := forced c a haS (hh S hS).2.1
        have hdS := forced d a haS (hh S hS).2.2.2.1
        have he : ({b,c,d} : Finset α) = S := Finset.eq_of_subset_of_card_le
          (by simp [Finset.insert_subset_iff,hbS,hcS,hdS]) (by simp [hu S hS,hbc,hbd,hcd])
        simp [← he]
  have hb := Finset.card_le_card hcover
  have hc := Finset.card_union_le A ({{a,c,d},{b,c,d}} : Finset (Finset α))
  have ht : ({{a,c,d},{b,c,d}} : Finset (Finset α)).card ≤ 2 := by
    have := Finset.card_insert_le ({a,c,d} : Finset α) ({{b,c,d}} : Finset (Finset α))
    simpa using this
  omega



/-- Two distinct triangular constraints with one common point admit only four triples. -/
theorem one_point_triangles_card_le_four
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (C D : Finset α) (a : α)
    (hC : C.card = 3) (hD : D.card = 3) (hCD : C ∩ D = {a})
    (hu : ∀ S ∈ F, S.card = 3)
    (hc : ∀ S ∈ F, 2 ≤ (S ∩ C).card) (hd : ∀ S ∈ F, 2 ≤ (S ∩ D).card) : F.card ≤ 4 := by
  classical
  have haC : a ∈ C := Finset.mem_inter.mp (hCD ▸ Finset.mem_singleton_self a) |>.1
  have haD : a ∈ D := Finset.mem_inter.mp (hCD ▸ Finset.mem_singleton_self a) |>.2
  let A := C.erase a
  let B := D.erase a
  have hA : A.card = 2 := by dsimp [A]; rw [Finset.card_erase_of_mem haC,hC]
  have hB : B.card = 2 := by dsimp [B]; rw [Finset.card_erase_of_mem haD,hD]
  have hcover : F ⊆ (A ×ˢ B).image (fun uv => ({a,uv.1,uv.2} : Finset α)) := by
    intro S hS
    have haS : a ∈ S := by
      have ht := intersections_have_common_point S C D (hu S hS) (hc S hS) (hd S hS)
      obtain ⟨q,hq⟩ := ht
      obtain ⟨hqS,hqE⟩ := Finset.mem_inter.mp hq
      have hqa : q = a := Finset.mem_singleton.mp (hCD ▸ hqE)
      simpa [hqa] using hqS
    have heC : ((S ∩ C).erase a).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨haS,haC⟩)]
      have := hc S hS
      omega
    have heD : ((S ∩ D).erase a).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem (Finset.mem_inter.mpr ⟨haS,haD⟩)]
      have := hd S hS
      omega
    obtain ⟨u,huE⟩ := heC
    obtain ⟨v,hvE⟩ := heD
    obtain ⟨hua,huI⟩ := Finset.mem_erase.mp huE
    obtain ⟨huS,huC⟩ := Finset.mem_inter.mp huI
    obtain ⟨hva,hvI⟩ := Finset.mem_erase.mp hvE
    obtain ⟨hvS,hvD⟩ := Finset.mem_inter.mp hvI
    have huv : u ≠ v := by
      intro he
      have ht : u ∈ C ∩ D := Finset.mem_inter.mpr ⟨huC,he.symm ▸ hvD⟩
      rw [hCD] at ht
      exact hua (Finset.mem_singleton.mp ht)
    have he : ({a,u,v} : Finset α) = S := Finset.eq_of_subset_of_card_le
      (by simp [Finset.insert_subset_iff,haS,huS,hvS])
      (by simp [hu S hS,Ne.symm hua,Ne.symm hva,huv])
    apply Finset.mem_image.mpr
    exact ⟨(u,v),Finset.mem_product.mpr
      ⟨Finset.mem_erase.mpr ⟨hua,huC⟩,Finset.mem_erase.mpr ⟨hva,hvD⟩⟩,he⟩
  exact (Finset.card_le_card hcover).trans ((Finset.card_image_le).trans (by simp [hA,hB]))



/-- A sunflower-free triple family crossing all edges of two distinct triangles
has cardinality at most four. No internal intersection hypothesis is needed. -/
theorem two_distinct_triangles_card_le_four
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (C D : Finset α)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hC : C.card = 3) (hD : D.card = 3) (hne : C ≠ D)
    (hhC : ∀ S ∈ F, ∀ P ∈ C.powersetCard 2, (S ∩ P).Nonempty)
    (hhD : ∀ S ∈ F, ∀ P ∈ D.powersetCard 2, (S ∩ P).Nonempty) : F.card ≤ 4 := by
  classical
  have hc (S) (hS : S ∈ F) := two_points_of_meets_pairs C S hC (hhC S hS)
  have hd (S) (hS : S ∈ F) := two_points_of_meets_pairs D S hD (hhD S hS)
  have he : (C ∩ D).card ≤ 2 := by
    by_contra hn
    have hEC : C ∩ D = C := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hED : C ∩ D = D := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    exact hne (hEC.symm.trans hED)
  by_cases hF : F.Nonempty
  · obtain ⟨S,hS⟩ := hF
    have hpos : 0 < (C ∩ D).card := by
      obtain ⟨x,hx⟩ := intersections_have_common_point S C D (hu S hS) (hc S hS) (hd S hS)
      exact Finset.card_pos.mpr ⟨x,(Finset.mem_inter.mp hx).2⟩
    by_cases he1 : (C ∩ D).card = 1
    · obtain ⟨a,ha⟩ := Finset.card_eq_one.mp he1
      exact one_point_triangles_card_le_four F C D a hC hD ha hu hc hd
    · have he2 : (C ∩ D).card = 2 := by omega
      obtain ⟨a,b,hab,habE⟩ := Finset.card_eq_two.mp he2
      have hc1 : (C \ D).card = 1 := by have := Finset.card_sdiff_add_card_inter C D; omega
      have hd1 : (D \ C).card = 1 := by
        have := Finset.card_sdiff_add_card_inter D C
        rw [Finset.inter_comm D C] at this
        omega
      obtain ⟨c,hcs⟩ := Finset.card_eq_one.mp hc1
      obtain ⟨d,hds⟩ := Finset.card_eq_one.mp hd1
      have hcp : c ∈ C ∧ c ∉ D := Finset.mem_sdiff.mp (hcs ▸ Finset.mem_singleton_self c)
      have hdp : d ∈ D ∧ d ∉ C := Finset.mem_sdiff.mp (hds ▸ Finset.mem_singleton_self d)
      have haCD : a ∈ C ∧ a ∈ D := Finset.mem_inter.mp (habE ▸ (by simp))
      have hbCD : b ∈ C ∧ b ∈ D := Finset.mem_inter.mp (habE ▸ (by simp))
      have hac : a ≠ c := fun hh => hcp.2 (hh ▸ haCD.2)
      have hbc : b ≠ c := fun hh => hcp.2 (hh ▸ hbCD.2)
      have had : a ≠ d := fun hh => hdp.2 (hh ▸ haCD.1)
      have hbd : b ≠ d := fun hh => hdp.2 (hh ▸ hbCD.1)
      have hcd : c ≠ d := fun hh => hdp.2 (hh ▸ hcp.1)
      have hCeq : C = {a,b,c} := by
        rw [← Finset.sdiff_union_inter C D,hcs,habE]
        ext q; simp
      have hDeq : D = {a,b,d} := by
        rw [← Finset.sdiff_union_inter D C,hds,Finset.inter_comm D C,habE]
        ext q; simp
      apply shared_edge_triangles_card_le_four F hu hf a b c d hab hac had hbc hbd hcd
      intro T hT
      refine ⟨hhC T hT {a,b} ?_,hhC T hT {a,c} ?_,hhC T hT {b,c} ?_,hhD T hT {a,d} ?_,hhD T hT {b,d} ?_⟩
      all_goals apply Finset.mem_powersetCard.mpr
      all_goals simp [hCeq,hDeq,Finset.insert_subset_iff,hab,hac,hbc,had,hbd]
  · have : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp [this]



/-- Canonical triangular edge classes are the two-element subsets of their support. -/
theorem triangle_edges_eq_powerset
    {α : Type*} [DecidableEq α] (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({{a,b},{a,c},{b,c}} : Finset (Finset α)) = ({a,b,c} : Finset α).powersetCard 2 := by
  ext P
  constructor
  · intro hP
    simp only [Finset.mem_insert,Finset.mem_singleton] at hP
    rcases hP with rfl | rfl | rfl
    all_goals apply Finset.mem_powersetCard.mpr
    all_goals simp [Finset.insert_subset_iff,hab,hac,hbc]
  · exact Erdos20Tetrahedron.pair_subset_triangle_mem a b c P

/-- Two saturated intersecting edge families crossed by at least five triples coincide. -/
theorem crossing_five_forces_triangles_equal
    {α : Type*} [DecidableEq α] (F G H : Finset (Finset α))
    (huF : ∀ S ∈ F, S.card = 3) (hfF : IsSunflowerFree F 3) (hF : 5 ≤ F.card)
    (huG : ∀ S ∈ G, S.card = 2) (hfG : IsSunflowerFree G 3)
    (hiG : ∀ S ∈ G, ∀ T ∈ G, (S ∩ T).Nonempty) (hG : G.card = 3)
    (huH : ∀ S ∈ H, S.card = 2) (hfH : IsSunflowerFree H 3)
    (hiH : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty) (hH : H.card = 3)
    (hcG : ∀ S ∈ F, ∀ T ∈ G, (S ∩ T).Nonempty)
    (hcH : ∀ S ∈ F, ∀ T ∈ H, (S ∩ T).Nonempty) : G = H := by
  obtain ⟨a,b,c,hab,hac,hbc,hGeq⟩ := intersecting_three_edges_triangle G huG
    (fun x => rank_two_three_petals_degree_le_two G huG hfG x) hiG hG
  obtain ⟨d,e,f,hde,hdf,hef,hHeq⟩ := intersecting_three_edges_triangle H huH
    (fun x => rank_two_three_petals_degree_le_two H huH hfH x) hiH hH
  rw [triangle_edges_eq_powerset a b c hab hac hbc] at hGeq
  rw [triangle_edges_eq_powerset d e f hde hdf hef] at hHeq
  by_cases hh : ({a,b,c} : Finset α) = {d,e,f}
  · rw [hGeq,hHeq,hh]
  · have h4 := two_distinct_triangles_card_le_four F {a,b,c} {d,e,f} huF hfF
      (by simp [hab,hac,hbc]) (by simp [hde,hdf,hef]) hh
      (by simpa [hGeq] using hcG) (by simpa [hHeq] using hcH)
    omega

/-- A large singleton exact trace synchronizes all disjoint saturated pair traces. -/
theorem large_singleton_saturated_pair_residuals_equal
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R C D : Finset α) (x : α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (hC : C.card = 2) (hD : D.card = 2) (hxC : x ∉ C) (hxD : x ∉ D)
    (hs : 5 ≤ (exactTrace F R {x}).card)
    (hc : (exactTrace F R C).card = 3) (hd : (exactTrace F R D).card = 3) :
    residualLink (exactTrace F R C) C = residualLink (exactTrace F R D) D := by
  let A := residualLink (exactTrace F R {x}) {x}
  let G := residualLink (exactTrace F R C) C
  let H := residualLink (exactTrace F R D) D
  apply crossing_five_forces_triangles_equal A G H
  · simpa [A] using residualLink_uniform (core := {x})
      (fun S hS => hu S (Finset.mem_filter.mp hS).1)
  · exact exact_trace_residual_free F R {x} 3 hf
  · simpa [A,exact_trace_card_residual] using hs
  · simpa [G,hC] using residualLink_uniform (core := C)
      (fun S hS => hu S (Finset.mem_filter.mp hS).1)
  · exact exact_trace_residual_free F R C 3 hf
  · exact exact_trace_residual_intersecting F R C 4 hR hu hf (by omega)
  · simpa [G,exact_trace_card_residual] using hc
  · simpa [H,hD] using residualLink_uniform (core := D)
      (fun S hS => hu S (Finset.mem_filter.mp hS).1)
  · exact exact_trace_residual_free F R D 3 hf
  · exact exact_trace_residual_intersecting F R D 4 hR hu hf (by omega)
  · simpa [H,exact_trace_card_residual] using hd
  · exact disjoint_traces_residual_cross_intersect F R {x} C hi (by simpa using hxC)
  · exact disjoint_traces_residual_cross_intersect F R {x} D hi (by simpa using hxD)

end Erdos20V9IntersectingTriangles
