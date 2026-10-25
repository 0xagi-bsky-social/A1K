import SunflowerLean.Erdos20ExtremalSupport

/-! Local structure of intersecting and extremal triple families. -/
namespace Erdos20ExtremalStructure
open Erdos20BCWConditional Erdos20StrictCore Erdos20RankThreeEven
open Erdos20GraphEquality Erdos20Tetrahedron Erdos20SharpTriples

/-- An intersecting triple family with a degree-six point consists precisely
of that point's six members. -/
theorem intersecting_degree_six_card_eq_six
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (x : α) (hd : (F.filter (fun S => x ∈ S)).card = 6) : F.card = 6 := by
  obtain ⟨a,b,c,d,e,f,hab,hac,hbc,hde,hdf,hef,hdis,hxout,hshape⟩ :=
    degree_six_triple_link_two_triangles F x hu hf hd
  have hcommon : ∀ S ∈ F, x ∈ S := by
    intro S hS
    by_contra hxS
    have hhit : ∀ P ∈ residualLink F {x}, (S ∩ P).Nonempty := by
      intro P hP
      obtain ⟨v,hv⟩ := hi S hS ({x} ∪ P) (core_union_residual_mem_family hP)
      obtain ⟨hvS,hvP⟩ := Finset.mem_inter.mp hv
      rcases Finset.mem_union.mp hvP with hvx | hvP
      · exact False.elim (hxS ((Finset.mem_singleton.mp hvx) ▸ hvS))
      · exact ⟨v,Finset.mem_inter.mpr ⟨hvS,hvP⟩⟩
    have hA : ({a,b,c} : Finset α).card = 3 := by simp [hab,hac,hbc]
    have hB : ({d,e,f} : Finset α).card = 3 := by simp [hde,hdf,hef]
    obtain ⟨P,hPA,hPS⟩ := contains_pair_of_meets_every_pair_of_triple {a,b,c} S hA
      (fun P hP => hhit P (by rw [hshape]; exact Finset.mem_union_left _ (pair_subset_triangle_mem a b c P hP)))
    obtain ⟨Q,hQB,hQS⟩ := contains_pair_of_meets_every_pair_of_triple {d,e,f} S hB
      (fun Q hQ => hhit Q (by rw [hshape]; exact Finset.mem_union_right _ (pair_subset_triangle_mem d e f Q hQ)))
    obtain ⟨hPsub,hPcard⟩ := Finset.mem_powersetCard.mp hPA
    obtain ⟨hQsub,hQcard⟩ := Finset.mem_powersetCard.mp hQB
    have hPQ : Disjoint P Q := by
      apply Finset.disjoint_left.mpr
      intro t htP htQ
      exact Finset.disjoint_left.mp hdis (hPsub htP) (hQsub htQ)
    have hle := Finset.card_le_card (Finset.union_subset hPS hQS)
    rw [Finset.card_union_of_disjoint hPQ,hPcard,hQcard,hu S hS] at hle
    omega
  have he : F.filter (fun S => x ∈ S) = F := Finset.filter_eq_self.mpr hcommon
  simpa [he] using hd

/-- An intersecting triple family with more than six members has every point degree at most five. -/
theorem intersecting_card_ge_seven_degree_le_five
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : 7 ≤ F.card) (x : α) :
    (F.filter (fun S => x ∈ S)).card ≤ 5 := by
  have hd := rank_three_degree_le_six F hu hf x
  by_contra hnot
  have hsix : (F.filter (fun S => x ∈ S)).card = 6 := by omega
  have he := intersecting_degree_six_card_eq_six F hu hf hi x hsix
  omega

/-- In particular, every point of an intersecting ten-member family has degree at most five. -/
theorem intersecting_ten_degree_le_five
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 10) (x : α) :
    (F.filter (fun S => x ∈ S)).card ≤ 5 :=
  intersecting_card_ge_seven_degree_le_five F hu hf hi (by omega) x

/-- The local degree alternatives yielded by equality in the three paired trace bounds. -/
def MemberDegreePattern {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (S : Finset α) : Prop :=
  (∀ x ∈ S, (F.filter (fun T => x ∈ T)).card = 4) ∨
  ((∀ x ∈ S, (F.filter (fun T => x ∈ T)).card = 3 ∨
      (F.filter (fun T => x ∈ T)).card = 5) ∧
    (S.filter (fun x => (F.filter (fun T => x ∈ T)).card = 3)).card ≤ 1)

/-- Once the local degree pattern holds, intersection propagates and excludes degree four. -/
theorem local_patterns_exclude_degree_four
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (hc : F.card = 10) (hp : ∀ S ∈ F, MemberDegreePattern F S)
    (x : α) (hx : x ∈ support F) : (F.filter (fun T => x ∈ T)).card ≠ 4 := by
  intro hd4
  obtain ⟨R,hR,hxR⟩ := Finset.mem_biUnion.mp hx
  have hR4 : ∀ y ∈ R, (F.filter (fun T => y ∈ T)).card = 4 := by
    rcases hp R hR with h | h
    · exact h
    · have he := h.1 x hxR
      omega
  have hS4 : ∀ S ∈ F, ∀ y ∈ S, (F.filter (fun T => y ∈ T)).card = 4 := by
    intro S hS
    obtain ⟨v,hv⟩ := hi S hS R hR
    have hvS := (Finset.mem_inter.mp hv).1
    have hv4 := hR4 v (Finset.mem_inter.mp hv).2
    rcases hp S hS with h | h
    · exact h
    · have he := h.1 v hvS
      omega
  have hall4 : ∀ y ∈ support F, (F.filter (fun T => y ∈ T)).card = 4 := by
    intro y hy
    obtain ⟨S,hS,hyS⟩ := Finset.mem_biUnion.mp hy
    exact hS4 S hS y hyS
  have hsum := Erdos20ExtremalSupport.support_degree_sum F 3 hu
  have he : (∑ y ∈ support F, (F.filter (fun T => y ∈ T)).card) = (support F).card * 4 := by
    calc
      _ = ∑ _y ∈ support F, 4 := Finset.sum_congr rfl hall4
      _ = _ := by simp
  rw [he,hc] at hsum
  omega

/-- Local trace-equality degree patterns force a ten-member intersecting family
onto six points, with every supported point having degree five. -/
theorem local_patterns_force_regular_six_support
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (hc : F.card = 10) (hp : ∀ S ∈ F, MemberDegreePattern F S) :
    (support F).card = 6 ∧ ∀ x ∈ support F, (F.filter (fun T => x ∈ T)).card = 5 := by
  classical
  have hn4 := local_patterns_exclude_degree_four F hu hi hc hp
  have hpat : ∀ S ∈ F,
      (∀ x ∈ S, (F.filter (fun T => x ∈ T)).card = 3 ∨ (F.filter (fun T => x ∈ T)).card = 5) ∧
      (S.filter (fun x => (F.filter (fun T => x ∈ T)).card = 3)).card ≤ 1 := by
    intro S hS
    rcases hp S hS with h | h
    · obtain ⟨x,hx⟩ := Finset.card_pos.mp (by rw [hu S hS]; decide : 0 < S.card)
      exact False.elim (hn4 x (member_subset_support hS hx) (h x hx))
    · exact h
  have hall : ∀ x ∈ support F,
      (F.filter (fun T => x ∈ T)).card = 3 ∨ (F.filter (fun T => x ∈ T)).card = 5 := by
    intro x hx
    obtain ⟨S,hS,hxS⟩ := Finset.mem_biUnion.mp hx
    exact (hpat S hS).1 x hxS
  let A := (support F).filter (fun x => (F.filter (fun T => x ∈ T)).card = 3)
  have hmeet : ∀ S ∈ F, (S ∩ A).card ≤ 1 := by
    intro S hS
    have he : S ∩ A = S.filter (fun x => (F.filter (fun T => x ∈ T)).card = 3) := by
      ext x
      simp only [Finset.mem_inter,Finset.mem_filter,A]
      exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,member_subset_support hS h.1,h.2⟩⟩
    rw [he]
    exact (hpat S hS).2
  have hAcap : A.card ≤ 3 := by
    have hiA := Erdos20Incidence.incidence_sum_eq F A
    have hlo : (∑ S ∈ F, (S ∩ A).card) ≤ 10 := by
      calc
        _ ≤ ∑ _S ∈ F, 1 := Finset.sum_le_sum hmeet
        _ = _ := by simp [hc]
    have hr : (∑ x ∈ A, (F.filter (fun T => x ∈ T)).card) = A.card * 3 := by
      calc
        _ = ∑ _x ∈ A, 3 := Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2)
        _ = _ := by simp
    rw [hiA,hr] at hlo
    omega
  have hindicator : (∑ x ∈ support F, if x ∈ A then 1 else 0) = A.card := by
    rw [← Finset.sum_filter]
    have he : (support F).filter (fun x => x ∈ A) = A := by
      ext x
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2,fun h => ⟨(Finset.mem_filter.mp h).1,h⟩⟩
    simp [he]
  have hpoint : ∀ x ∈ support F,
      (F.filter (fun T => x ∈ T)).card + 2 * (if x ∈ A then 1 else 0) = 5 := by
    intro x hx
    rcases hall x hx with hd | hd
    · have hxA : x ∈ A := Finset.mem_filter.mpr ⟨hx,hd⟩
      simp [hd,hxA]
    · have hxA : x ∉ A := by intro hm; have := (Finset.mem_filter.mp hm).2; omega
      simp [hd,hxA]
  have heq : 30 + 2 * A.card = (support F).card * 5 := by
    have he := Finset.sum_congr rfl hpoint
    rw [Finset.sum_add_distrib,← Finset.mul_sum,hindicator,
      Erdos20ExtremalSupport.support_degree_sum F 3 hu,hc] at he
    simpa using he
  have hA0 : A.card = 0 := by omega
  have hs : (support F).card = 6 := by omega
  refine ⟨hs,?_⟩
  intro x hx
  rcases hall x hx with hd | hd
  · have hxA : x ∈ A := Finset.mem_filter.mpr ⟨hx,hd⟩
    have hpos := Finset.card_pos.mpr (show A.Nonempty from ⟨x,hxA⟩)
    omega
  · exact hd

end Erdos20ExtremalStructure
