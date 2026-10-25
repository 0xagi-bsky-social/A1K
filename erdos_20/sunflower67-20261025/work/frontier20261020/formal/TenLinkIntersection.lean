import SunflowerLean.Erdos20DesignNormalForm
import SunflowerLean.Erdos20GraphEquality

namespace FrontierTenLinkIntersection
open Erdos20BCWConditional Erdos20StrictCore Erdos20RankThree
open Erdos20CrossBounds Erdos20GraphEquality Erdos20DesignNormalForm Erdos20MixedCross

/-- Five blocks through a point cannot be covered by the two pair-stars,
each of size at most two. This supplies the singleton-core obstruction in
the split-pair completion argument. -/
theorem ten_point_has_block_avoiding_two
    {α : Type*} [DecidableEq α] (H : Finset (Finset α))
    (hu : ∀ P ∈ H, P.card = 3) (hf : IsSunflowerFree H 3)
    (hi : ∀ P ∈ H, ∀ Q ∈ H, (P ∩ Q).Nonempty) (hc : H.card = 10)
    (q r s : α) (hq : q ∈ support H) (hqr : q ≠ r) (hqs : q ≠ s) :
    ∃ T ∈ H, q ∈ T ∧ r ∉ T ∧ s ∉ T := by
  classical
  have hdegree := (Erdos20V5Frontier.intersecting_ten_design H hu hf hi hc).2.1 q hq
  have hqr2 := triple_pair_degree_le_two H hu hf ({q,r} : Finset α) (by simp [hqr])
  have hqs2 := triple_pair_degree_le_two H hu hf ({q,s} : Finset α) (by simp [hqs])
  by_contra hn
  push_neg at hn
  have hsub : H.filter (fun T => q ∈ T) ⊆
      H.filter (fun T => ({q,r} : Finset α) ⊆ T) ∪
      H.filter (fun T => ({q,s} : Finset α) ⊆ T) := by
    intro T hT
    obtain ⟨hTH,hqT⟩ := Finset.mem_filter.mp hT
    by_cases hrT : r ∈ T
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨hTH,by simp [Finset.insert_subset_iff,hqT,hrT]⟩)
    · have hsT := hn T hTH hqT hrT
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨hTH,by simp [Finset.insert_subset_iff,hqT,hsT]⟩)
  have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

/-- In a point link of the extremal six-point design, an intersecting
subfamily of edges has at most two members. This is the abstract C5 property
needed by the split-pair completion argument. -/
theorem ten_point_link_intersecting_subfamily_le_two
    {α : Type*} [DecidableEq α] (H G : Finset (Finset α))
    (hu : ∀ P ∈ H, P.card = 3) (hf : IsSunflowerFree H 3)
    (hi : ∀ P ∈ H, ∀ Q ∈ H, (P ∩ Q).Nonempty) (hc : H.card = 10)
    (a : α) (hG : G ⊆ residualLink H {a})
    (hGi : ∀ P ∈ G, ∀ Q ∈ G, (P ∩ Q).Nonempty) : G.card ≤ 2 := by
  have hLu : ∀ P ∈ residualLink H {a}, P.card = 2 := by
    simpa using residualLink_uniform (core := ({a} : Finset α)) hu
  have hGu : ∀ P ∈ G, P.card = 2 := fun P hP => hLu P (hG hP)
  have hGf : IsSunflowerFree G 3 := fun A hA hsun =>
    residualLink_sunflowerFree hf A (hA.trans hG) hsun
  have hthree := intersecting_rank_two_three_petals_card_le_three G hGu hGf hGi
  by_contra hn
  have hGc : G.card = 3 := by omega
  obtain ⟨b,c,d,hbc,hbd,hcd,hshape⟩ := intersecting_three_edges_triangle G hGu
    (fun x => rank_two_three_petals_degree_le_two G hGu hGf x) hGi hGc
  have hbcG : ({b,c} : Finset α) ∈ G := by simp [hshape]
  have hbdG : ({b,d} : Finset α) ∈ G := by simp [hshape]
  have hcdG : ({c,d} : Finset α) ∈ G := by simp [hshape]
  have habc : ({a,b,c} : Finset α) ∈ H := by
    convert core_union_residual_mem_family (hG hbcG) using 1
  have habd : ({a,b,d} : Finset α) ∈ H := by
    convert core_union_residual_mem_family (hG hbdG) using 1
  have hacd : ({a,c,d} : Finset α) ∈ H := by
    convert core_union_residual_mem_family (hG hcdG) using 1
  have hab : a ≠ b := by
    intro he
    have h := hu _ habc
    simp [he] at h
    have : ({b,c} : Finset α).card ≤ 2 := Finset.card_le_two
    omega
  have hac : a ≠ c := by
    intro he
    have h := hu _ habc
    simp [he] at h
    have : ({b,c} : Finset α).card ≤ 2 := Finset.card_le_two
    omega
  have had : a ≠ d := by
    intro he
    have h := hu _ habd
    simp [he] at h
    have : ({b,d} : Finset α).card ≤ 2 := Finset.card_le_two
    omega
  exact ten_forbids_three_faces H hu hf hi hc a b c d hab hac had hbc hbd hcd habc habd hacd

/-- An injectively represented two-coordinate family has at most four
members when both coordinate projections are intersecting subfamilies of
point links of extremal ten-designs. -/
theorem two_ten_link_coordinates_card_le_four
    {α : Type*} [DecidableEq α] {β : Type*} [DecidableEq β]
    (H K : Finset (Finset α)) (G : Finset β) (p q : β → Finset α)
    (hHu : ∀ P ∈ H, P.card = 3) (hKu : ∀ P ∈ K, P.card = 3)
    (hHf : IsSunflowerFree H 3) (hKf : IsSunflowerFree K 3)
    (hHi : ∀ P ∈ H, ∀ Q ∈ H, (P ∩ Q).Nonempty)
    (hKi : ∀ P ∈ K, ∀ Q ∈ K, (P ∩ Q).Nonempty)
    (hHc : H.card = 10) (hKc : K.card = 10)
    (a b : α)
    (hp : ∀ t ∈ G, p t ∈ residualLink H {a})
    (hq : ∀ t ∈ G, q t ∈ residualLink K {b})
    (hpi : ∀ s ∈ G, ∀ t ∈ G, (p s ∩ p t).Nonempty)
    (hqi : ∀ s ∈ G, ∀ t ∈ G, (q s ∩ q t).Nonempty)
    (hinj : ∀ s ∈ G, ∀ t ∈ G, p s = p t → q s = q t → s = t) :
    G.card ≤ 4 := by
  classical
  have hpSub : G.image p ⊆ residualLink H {a} := by
    intro P hP
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hP
    exact hp t ht
  have hqSub : G.image q ⊆ residualLink K {b} := by
    intro P hP
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hP
    exact hq t ht
  have hpInt : ∀ P ∈ G.image p, ∀ Q ∈ G.image p, (P ∩ Q).Nonempty := by
    intro P hP Q hQ
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hQ
    exact hpi s hs t ht
  have hqInt : ∀ P ∈ G.image q, ∀ Q ∈ G.image q, (P ∩ Q).Nonempty := by
    intro P hP Q hQ
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hQ
    exact hqi s hs t ht
  have hp2 := ten_point_link_intersecting_subfamily_le_two H (G.image p)
    hHu hHf hHi hHc a hpSub hpInt
  have hq2 := ten_point_link_intersecting_subfamily_le_two K (G.image q)
    hKu hKf hKi hKc b hqSub hqInt
  have hInjective : Set.InjOn (fun t => (p t,q t)) (↑G : Set β) := by
    intro s hs t ht he
    exact hinj s hs t ht (congrArg Prod.fst he) (congrArg Prod.snd he)
  have hsub : G.image (fun t => (p t,q t)) ⊆ (G.image p) ×ˢ (G.image q) := by
    intro z hz
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨t,ht,rfl⟩,
      Finset.mem_image.mpr ⟨t,ht,rfl⟩⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hInjective,Finset.card_product] at hh
  exact hh.trans (by nlinarith)

end FrontierTenLinkIntersection
