import SunflowerLean.Erdos20V10Profile54Bridge
import SunflowerLean.Erdos20V8Targets

namespace Erdos20V10Profile54DegreeCap
open Erdos20BCWConditional Erdos20StrictCore Erdos20RankThree Erdos20RankFour
open Erdos20V8Global Erdos20V8Boundary Erdos20V8Targets Erdos20DegreeCongruences
open Erdos20V10Profile54Bridge

/-- A family with all point degrees at most18 cannot have every closed
meeting neighborhood of size at least54. The proof uses actual singleton
trace subfamilies, not just a feasible arithmetic profile. -/
theorem no_all_meeting_fifty_four_of_degree_cap_eighteen
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card=4) (hf : IsSunflowerFree F 3)
    (hne : F.Nonempty) (hd : ∀ x, degree F x≤18)
    (hm : ∀ R ∈ F, 54 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card) : False := by
  classical
  obtain ⟨R,hR⟩ := hne
  obtain ⟨_,x,hx,hsat⟩ := meeting_at_least_fifty_four_degree_cap_eighteen_traces F hu hf hd R hR (hm R hR)
  let L := residualLink F {x}
  let H := residualLink (exactTrace F R {x}) {x}
  have hHL : H ⊆ L := by
    intro P hP
    obtain ⟨S,hS,hxS,hSP⟩ := mem_residualLink_iff.mp hP
    exact mem_residualLink_iff.mpr ⟨S,(Finset.mem_filter.mp hS).1,hxS,hSP⟩
  have hHc : H.card=10 := by simpa [H,exact_trace_card_residual] using hsat
  have hHi : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty :=
    exact_trace_residual_intersecting F R {x} 4 hR hu hf (by simp)
  obtain ⟨A,hAH⟩ := Finset.card_pos.mp (show 0<H.card by omega)
  obtain ⟨S,hSC,hxS,hSA⟩ := mem_residualLink_iff.mp hAH
  have hSF : S ∈ F := (Finset.mem_filter.mp hSC).1
  have hxS' : x ∈ S := Finset.singleton_subset_iff.mp hxS
  have hlo := (meeting_at_least_fifty_four_degree_cap_eighteen_traces F hu hf hd S hSF (hm S hSF)).1 x hxS'
  have hsub : exactTrace L A ∅ ⊆ L \ H := by
    intro B hB
    obtain ⟨hBL,hBA⟩ := Finset.mem_filter.mp hB
    refine Finset.mem_sdiff.mpr ⟨hBL,?_⟩
    intro hBH
    have hh := hHi B hBH A hAH
    rw [hBA] at hh
    exact Finset.not_nonempty_empty hh
  have hle := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hHL,hHc] at hle
  have hLc : L.card≤18 := by simpa [L,card_residualLink,upperStar,degree] using hd x
  have hEq : (exactTrace F S {x}).card = (exactTrace L A ∅).card := by
    rw [← exact_trace_card_residual F S {x}]
    have hh := singleton_residual_eq_empty_link_trace F S x hxS'
    rw [hSA] at hh
    exact congrArg Finset.card hh
  rw [hEq] at hlo
  omega

/-- Under point-degree cap18, some actual anchor meets at most53 members. -/
theorem exists_anchor_meeting_le_fifty_three_of_degree_cap_eighteen
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card=4) (hf : IsSunflowerFree F 3)
    (hne : F.Nonempty) (hd : ∀ x, degree F x≤18) :
    ∃ R ∈ F, (F.filter (fun S => (S ∩ R).Nonempty)).card≤53 := by
  classical
  by_contra hn
  push_neg at hn
  exact no_all_meeting_fifty_four_of_degree_cap_eighteen F hu hf hne hd
    (fun R hR => by have := hn R hR; omega)

/-- The conditional unrestricted upper80 for the full degree-at-most18 class.
The universal intersecting bound27 remains an explicit ordinary argument. -/
theorem card_le_eighty_of_degree_cap_eighteen
    (hI : IntersectingRankFourUpper 27)
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card=4) (hf : IsSunflowerFree F 3)
    (hd : ∀ x, degree F x≤18) : F.card≤80 := by
  classical
  by_cases hne : F.Nonempty
  · obtain ⟨R,hR,hmeet⟩ := exists_anchor_meeting_le_fifty_three_of_degree_cap_eighteen F hu hf hne hd
    let G := F.filter (fun S => S ∩ R=∅)
    have hGF : G ⊆ F := Finset.filter_subset _ _
    have hGu : ∀ S ∈ G, S.card=4 := fun S hS => hu S (hGF hS)
    have hGf : IsSunflowerFree G 3 := fun H hH hs => hf H (hH.trans hGF) hs
    have hGi : ∀ S ∈ G, ∀ T ∈ G, (S ∩ T).Nonempty := by
      intro S hS T hT
      exact disjoint_anchor_family_intersecting F R hR
        (Finset.card_pos.mp (by rw [hu R hR]; decide)) hf S hS T hT
        (Finset.card_pos.mp (by rw [hGu S hS]; decide))
        (Finset.card_pos.mp (by rw [hGu T hT]; decide))
    have h27 := hI G hGu hGf hGi
    have hp := Finset.filter_card_add_filter_neg_card_eq_card (s := F) (p := fun S => (S ∩ R).Nonempty)
    simp only [Finset.not_nonempty_iff_eq_empty] at hp
    change (F.filter (fun S => (S ∩ R).Nonempty)).card+G.card=F.card at hp
    omega
  · have hF : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hF]

end Erdos20V10Profile54DegreeCap
