import TenLinkIntersection

namespace FrontierCompletionCompatibility
open Erdos20BCWConditional Erdos20StrictCore Erdos20RankThree
open FrontierTenLinkIntersection

/-- Two intersecting edges in a point link admit a block of the ten-design
whose traces on both edges equal their mutual intersection. -/
theorem intersecting_link_edges_have_shared_block_trace
    {α : Type*} [DecidableEq α] (H : Finset (Finset α))
    (hu : ∀ P ∈ H, P.card = 3) (hf : IsSunflowerFree H 3)
    (hi : ∀ P ∈ H, ∀ Q ∈ H, (P ∩ Q).Nonempty) (hc : H.card = 10)
    (a : α) (P Q : Finset α)
    (hP : P ∈ residualLink H {a}) (hQ : Q ∈ residualLink H {a})
    (hPQ : (P ∩ Q).Nonempty) :
    ∃ T ∈ H, T ∩ P = P ∩ Q ∧ T ∩ Q = P ∩ Q := by
  classical
  have huL : ∀ P ∈ residualLink H {a}, P.card = 2 := by
    simpa using residualLink_uniform (core := ({a} : Finset α)) hu
  have hP2 := huL P hP
  have hQ2 := huL Q hQ
  have hPmem : insert a P ∈ H := by
    convert core_union_residual_mem_family hP using 1
  have hPS : P ⊆ support H :=
    Finset.Subset.trans (Finset.subset_insert _ _) (member_subset_support hPmem)
  by_cases he : P = Q
  · subst Q
    refine ⟨insert a P,hPmem,?_,?_⟩ <;> simp
  obtain ⟨b,hb⟩ := hPQ
  obtain ⟨hbP,hbQ⟩ := Finset.mem_inter.mp hb
  have hPe : (P.erase b).card = 1 := by rw [Finset.card_erase_of_mem hbP,hP2]
  have hQe : (Q.erase b).card = 1 := by rw [Finset.card_erase_of_mem hbQ,hQ2]
  obtain ⟨r,hr⟩ := Finset.card_eq_one.mp hPe
  obtain ⟨s,hs⟩ := Finset.card_eq_one.mp hQe
  have hPshape : P = {b,r} := by rw [← Finset.insert_erase hbP,hr]
  have hQshape : Q = {b,s} := by rw [← Finset.insert_erase hbQ,hs]
  have hbr : b ≠ r := by intro h; have := hP2; simp [hPshape,h] at this
  have hbs : b ≠ s := by intro h; have := hQ2; simp [hQshape,h] at this
  have hrs : r ≠ s := by intro h; exact he (by rw [hPshape,hQshape,h])
  obtain ⟨T,hTH,hbT,hrT,hsT⟩ :=
    ten_point_has_block_avoiding_two H hu hf hi hc b r s (hPS hbP) hbr hbs
  refine ⟨T,hTH,?_,?_⟩
  · ext z
    simp only [hPshape,hQshape,Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
    aesop
  · ext z
    simp only [hPshape,hQshape,Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
    aesop

/-- For two distinct intersecting completions, disjoint tails outside one
design would create a sunflower with a member of its high star. Consequently
the tail projections must intersect. -/
theorem completion_tail_intersects
    {α : Type*} [DecidableEq α] (F H : Finset (Finset α))
    (hfF : IsSunflowerFree F 3)
    (hu : ∀ P ∈ H, P.card = 3) (hf : IsSunflowerFree H 3)
    (hi : ∀ P ∈ H, ∀ Q ∈ H, (P ∩ Q).Nonempty) (hc : H.card = 10)
    (x a : α) (hstar : ∀ T ∈ H, insert x T ∈ F)
    (P P' Q Q' : Finset α)
    (hP : P ∈ residualLink H {a}) (hP' : P' ∈ residualLink H {a})
    (hQ : Disjoint Q (support H)) (hQ' : Disjoint Q' (support H))
    (hS : P ∪ Q ∈ F) (hS' : P' ∪ Q' ∈ F)
    (hx : x ∉ P ∪ Q) (hx' : x ∉ P' ∪ Q')
    (hne : P ∪ Q ≠ P' ∪ Q')
    (hmeet : ((P ∪ Q) ∩ (P' ∪ Q')).Nonempty) :
    (Q ∩ Q').Nonempty := by
  classical
  by_contra hn
  have hQQ : Disjoint Q Q' :=
    Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp hn)
  have hPm : insert a P ∈ H := by
    convert core_union_residual_mem_family hP using 1
  have hP'm : insert a P' ∈ H := by
    convert core_union_residual_mem_family hP' using 1
  have hPS : P ⊆ support H :=
    Finset.Subset.trans (Finset.subset_insert _ _) (member_subset_support hPm)
  have hP'S : P' ⊆ support H :=
    Finset.Subset.trans (Finset.subset_insert _ _) (member_subset_support hP'm)
  have hPQ' : Disjoint P Q' := (hQ'.mono_right hPS).symm
  have hQP' : Disjoint Q P' := hQ.mono_right hP'S
  have hInt : (P ∪ Q) ∩ (P' ∪ Q') = P ∩ P' := by
    ext z
    simp only [Finset.mem_inter,Finset.mem_union]
    constructor
    · rintro ⟨hzP | hzQ,hzP' | hzQ'⟩
      · exact ⟨hzP,hzP'⟩
      · exact False.elim (Finset.disjoint_left.mp hPQ' hzP hzQ')
      · exact False.elim (Finset.disjoint_left.mp hQP' hzQ hzP')
      · exact False.elim (Finset.disjoint_left.mp hQQ hzQ hzQ')
    · rintro ⟨hzP,hzP'⟩
      exact ⟨Or.inl hzP,Or.inl hzP'⟩
  have hPP : (P ∩ P').Nonempty := by rwa [hInt] at hmeet
  obtain ⟨T,hTH,hTP,hTP'⟩ :=
    intersecting_link_edges_have_shared_block_trace H hu hf hi hc a P P' hP hP' hPP
  have hTQ : Disjoint T Q := (hQ.mono_right (member_subset_support hTH)).symm
  have hTQ' : Disjoint T Q' := (hQ'.mono_right (member_subset_support hTH)).symm
  have hTS : insert x T ∩ (P ∪ Q) = P ∩ P' := by
    calc
      _ = T ∩ P := by
        ext z
        simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_union]
        constructor
        · rintro ⟨rfl | hzT,hzP | hzQ⟩
          · exact False.elim (hx (Finset.mem_union_left _ hzP))
          · exact False.elim (hx (Finset.mem_union_right _ hzQ))
          · exact ⟨hzT,hzP⟩
          · exact False.elim (Finset.disjoint_left.mp hTQ hzT hzQ)
        · rintro ⟨hzT,hzP⟩
          exact ⟨Or.inr hzT,Or.inl hzP⟩
      _ = _ := hTP
  have hTS' : insert x T ∩ (P' ∪ Q') = P ∩ P' := by
    calc
      _ = T ∩ P' := by
        ext z
        simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_union]
        constructor
        · rintro ⟨rfl | hzT,hzP | hzQ⟩
          · exact False.elim (hx' (Finset.mem_union_left _ hzP))
          · exact False.elim (hx' (Finset.mem_union_right _ hzQ))
          · exact ⟨hzT,hzP⟩
          · exact False.elim (Finset.disjoint_left.mp hTQ' hzT hzQ)
        · rintro ⟨hzT,hzP⟩
          exact ⟨Or.inr hzT,Or.inl hzP⟩
      _ = _ := hTP'
  have hnS : insert x T ≠ P ∪ Q := by
    intro he
    exact hx (he ▸ Finset.mem_insert_self x T)
  have hnS' : insert x T ≠ P' ∪ Q' := by
    intro he
    exact hx' (he ▸ Finset.mem_insert_self x T)
  apply hfF {insert x T,P ∪ Q,P' ∪ Q'}
  · intro S hmem
    simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hstar T hTH
    · exact hS
    · exact hS'
  · exact sunflower_three_of_intersections _ _ _ _ hnS hnS' hne hTS hTS' hInt

/-- Full normalized split-pair bound. An intersecting family of completions,
each formed by one edge from each of two disjoint ten-design point links,
has at most four members when both ten-design high stars occur in the
same sunflower-free family. -/
theorem split_completions_card_le_four
    {α : Type*} [DecidableEq α] (F H K G : Finset (Finset α))
    (hfF : IsSunflowerFree F 3)
    (hHu : ∀ P ∈ H, P.card = 3) (hKu : ∀ P ∈ K, P.card = 3)
    (hHf : IsSunflowerFree H 3) (hKf : IsSunflowerFree K 3)
    (hHi : ∀ P ∈ H, ∀ Q ∈ H, (P ∩ Q).Nonempty)
    (hKi : ∀ P ∈ K, ∀ Q ∈ K, (P ∩ Q).Nonempty)
    (hHc : H.card = 10) (hKc : K.card = 10)
    (hdis : Disjoint (support H) (support K))
    (x a b : α)
    (hstarH : ∀ T ∈ H, insert x T ∈ F)
    (hstarK : ∀ T ∈ K, insert x T ∈ F)
    (p q : Finset α → Finset α)
    (hGF : G ⊆ F)
    (hp : ∀ S ∈ G, p S ∈ residualLink H {a})
    (hq : ∀ S ∈ G, q S ∈ residualLink K {b})
    (hshape : ∀ S ∈ G, S = p S ∪ q S)
    (hx : ∀ S ∈ G, x ∉ S)
    (hGi : ∀ S ∈ G, ∀ T ∈ G, (S ∩ T).Nonempty) :
    G.card ≤ 4 := by
  classical
  have hPS : ∀ S ∈ G, p S ⊆ support H := by
    intro S hS
    have hm : insert a (p S) ∈ H := by
      convert core_union_residual_mem_family (hp S hS) using 1
    exact Finset.Subset.trans (Finset.subset_insert _ _) (member_subset_support hm)
  have hQS : ∀ S ∈ G, q S ⊆ support K := by
    intro S hS
    have hm : insert b (q S) ∈ K := by
      convert core_union_residual_mem_family (hq S hS) using 1
    exact Finset.Subset.trans (Finset.subset_insert _ _) (member_subset_support hm)
  have hpi : ∀ S ∈ G, ∀ T ∈ G, (p S ∩ p T).Nonempty := by
    intro S hS T hT
    by_cases he : S = T
    · subst T
      rw [Finset.inter_self]
      have hc : (p S).card = 2 := by
        simpa using residualLink_uniform (core := ({a} : Finset α)) hHu (p S) (hp S hS)
      exact Finset.card_pos.mp (by omega)
    have hSshape : S = q S ∪ p S := (hshape S hS).trans (Finset.union_comm _ _)
    have hTshape : T = q T ∪ p T := (hshape T hT).trans (Finset.union_comm _ _)
    apply completion_tail_intersects F K hfF hKu hKf hKi hKc x b hstarK
      (q S) (q T) (p S) (p T) (hq S hS) (hq T hT)
      (hdis.mono_left (hPS S hS)) (hdis.mono_left (hPS T hT))
    · rw [← hSshape]; exact hGF hS
    · rw [← hTshape]; exact hGF hT
    · rw [← hSshape]; exact hx S hS
    · rw [← hTshape]; exact hx T hT
    · rw [← hSshape,← hTshape]; exact he
    · rw [← hSshape,← hTshape]; exact hGi S hS T hT
  have hqi : ∀ S ∈ G, ∀ T ∈ G, (q S ∩ q T).Nonempty := by
    intro S hS T hT
    by_cases he : S = T
    · subst T
      rw [Finset.inter_self]
      have hc : (q S).card = 2 := by
        simpa using residualLink_uniform (core := ({b} : Finset α)) hKu (q S) (hq S hS)
      exact Finset.card_pos.mp (by omega)
    apply completion_tail_intersects F H hfF hHu hHf hHi hHc x a hstarH
      (p S) (p T) (q S) (q T) (hp S hS) (hp T hT)
      (hdis.symm.mono_left (hQS S hS)) (hdis.symm.mono_left (hQS T hT))
    · rw [← hshape S hS]; exact hGF hS
    · rw [← hshape T hT]; exact hGF hT
    · rw [← hshape S hS]; exact hx S hS
    · rw [← hshape T hT]; exact hx T hT
    · rw [← hshape S hS,← hshape T hT]; exact he
    · rw [← hshape S hS,← hshape T hT]; exact hGi S hS T hT
  apply two_ten_link_coordinates_card_le_four H K G p q
    hHu hKu hHf hKf hHi hKi hHc hKc a b hp hq hpi hqi
  intro S hS T hT hpq hqq
  rw [hshape S hS,hshape T hT,hpq,hqq]

end FrontierCompletionCompatibility
