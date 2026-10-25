import MeetingDefect
import SunflowerLean.Erdos20V13Boundary

namespace FrontierProfileAOutside
open Erdos20BCWConditional Erdos20StrictCore Erdos20RankThree
open Erdos20DegreeCongruences Erdos20ExtremalTransversals

/-- Two disjoint members omitting a point must jointly meet every member of
that point's residual link; otherwise the three original members are disjoint. -/
theorem disjoint_rows_union_hits_link
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (x : α) (R S : Finset α) (hR : R ∈ F) (hS : S ∈ F)
    (hxR : x ∉ R) (hxS : x ∉ S) (hRS : Disjoint R S) :
    ∀ P ∈ residualLink F {x}, (P ∩ (R ∪ S)).Nonempty := by
  intro P hP
  have hPF : insert x P ∈ F := by simpa using core_union_residual_mem_family hP
  by_contra hn
  have hPR : Disjoint (insert x P) R := by
    apply Finset.disjoint_left.mpr
    intro v hv hvR
    rcases Finset.mem_insert.mp hv with rfl | hvP
    · exact hxR hvR
    · exact hn ⟨v,Finset.mem_inter.mpr ⟨hvP,Finset.mem_union_left S hvR⟩⟩
  have hPS : Disjoint (insert x P) S := by
    apply Finset.disjoint_left.mpr
    intro v hv hvS
    rcases Finset.mem_insert.mp hv with rfl | hvP
    · exact hxS hvS
    · exact hn ⟨v,Finset.mem_inter.mpr ⟨hvP,Finset.mem_union_right R hvS⟩⟩
  have hm := disjoint_anchor_family_intersecting F (insert x P) hPF
    (Finset.insert_nonempty x P) hf R
    (Finset.mem_filter.mpr ⟨hR,Finset.disjoint_iff_inter_eq_empty.mp hPR.symm⟩) S
    (Finset.mem_filter.mpr ⟨hS,Finset.disjoint_iff_inter_eq_empty.mp hPS.symm⟩)
    (Finset.card_pos.mp (by rw [hu R hR]; decide))
    (Finset.card_pos.mp (by rw [hu S hS]; decide))
  rw [Finset.disjoint_iff_inter_eq_empty.mp hRS] at hm
  exact Finset.not_nonempty_empty hm

/-- If the link has twenty members, two disjoint four-sets omitting its center
have at most two points in total outside its support. -/
theorem disjoint_rows_outside_sum_le_two
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (x : α) (hc : (residualLink F {x}).card = 20)
    (O : Finset α) (hOU : Disjoint O (support (residualLink F {x})))
    (R S : Finset α) (hR : R ∈ F) (hS : S ∈ F)
    (hxR : x ∉ R) (hxS : x ∉ S) (hRS : Disjoint R S) :
    (R ∩ O).card + (S ∩ O).card ≤ 2 := by
  let L := residualLink F {x}
  let C := (R ∪ S) ∩ support L
  have hLu : ∀ P ∈ L, P.card = 3 := by
    simpa [L] using residualLink_uniform (core := ({x} : Finset α)) hu
  have hhit := disjoint_rows_union_hits_link F hu hf x R S hR hS hxR hxS hRS
  have hCmin : 6 ≤ C.card := extremal_twenty_transversal_card_ge_six L hLu
    (residualLink_sunflowerFree hf) hc C
    (transversal_restrict_support L L (R ∪ S) (Finset.Subset.refl _) hhit)
  have hROSO : Disjoint (R ∩ O) (S ∩ O) :=
    hRS.mono Finset.inter_subset_left Finset.inter_subset_left
  have hCO : Disjoint C ((R ∩ O) ∪ (S ∩ O)) := by
    apply Finset.disjoint_left.mpr
    intro v hvC hvO
    have hvU : v ∈ support L := (Finset.mem_inter.mp hvC).2
    have hvO' : v ∈ O := by
      rcases Finset.mem_union.mp hvO with hvR | hvS
      · exact (Finset.mem_inter.mp hvR).2
      · exact (Finset.mem_inter.mp hvS).2
    exact Finset.disjoint_left.mp hOU hvO' hvU
  have hsub : C ∪ ((R ∩ O) ∪ (S ∩ O)) ⊆ R ∪ S := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvC | hvO
    · exact (Finset.mem_inter.mp hvC).1
    · rcases Finset.mem_union.mp hvO with hvR | hvS
      · exact Finset.mem_union_left S (Finset.mem_inter.mp hvR).1
      · exact Finset.mem_union_right R (Finset.mem_inter.mp hvS).1
  have hn := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hCO,Finset.card_union_of_disjoint hROSO,
    Finset.card_union_of_disjoint hRS,hu R hR,hu S hS] at hn
  omega

/-- Each member of a sixty-one-member residual family of maximum degree
nineteen has a disjoint partner. -/
theorem sixty_one_degree_nineteen_disjoint_partner
    {α : Type*} [DecidableEq α] (H : Finset (Finset α))
    (hu : ∀ R ∈ H, R.card = 4) (hf : IsSunflowerFree H 3)
    (hc : H.card = 61) (hd : ∀ v, degree H v ≤ 19)
    (R : Finset α) (hR : R ∈ H) :
    ∃ S ∈ H, Disjoint R S := by
  have hs : (∑ v ∈ R, degree H v) ≤ 76 := by
    calc
      _ ≤ ∑ _v ∈ R, 19 := Finset.sum_le_sum (fun v _ => hd v)
      _ = 76 := by simp [hu R hR]
  have hb := FrontierMeetingDefect.twice_card_le_twice_disjoint_add_degree_sum_add_thirty_eight
    H R hR hu hf
  have hp : 0 < (H.filter (fun S => S ∩ R = ∅)).card := by omega
  obtain ⟨S,hS⟩ := Finset.card_pos.mp hp
  obtain ⟨hSH,hSR⟩ := Finset.mem_filter.mp hS
  exact ⟨S,hSH,(Finset.disjoint_iff_inter_eq_empty.mpr hSR).symm⟩

/-- The outsider cap is derived from the actual original family, its extremal
link, and the residual family, rather than inserted as a search assumption. -/
theorem residual_sixty_one_outside_card_le_two
    {α : Type*} [DecidableEq α] (F H : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (hHF : H ⊆ F) (hHc : H.card = 61) (hd : ∀ v, degree H v ≤ 19)
    (x : α) (hxH : ∀ R ∈ H, x ∉ R)
    (hc : (residualLink F {x}).card = 20)
    (O : Finset α) (hOU : Disjoint O (support (residualLink F {x}))) :
    ∀ R ∈ H, (R ∩ O).card ≤ 2 := by
  intro R hR
  have hHu : ∀ S ∈ H, S.card = 4 := fun S hS => hu S (hHF hS)
  have hHf : IsSunflowerFree H 3 := fun G hG hsun => hf G (hG.trans hHF) hsun
  obtain ⟨S,hS,hRS⟩ := sixty_one_degree_nineteen_disjoint_partner H hHu hHf hHc hd R hR
  have hb := disjoint_rows_outside_sum_le_two F hu hf x hc O hOU R S
    (hHF hR) (hHF hS) (hxH R hR) (hxH S hS) hRS
  omega

end FrontierProfileAOutside
