import SunflowerLean.Erdos20V10DisjointDegree
import SunflowerLean.Erdos20V10Profile54ScoreBridge

namespace Erdos20V10MinimumDegree
open Erdos20BCWConditional Erdos20StrictCore Erdos20RankThree
open Erdos20DegreeCongruences Erdos20V8Global Erdos20V10DisjointDegree
open Erdos20V10Profile54Bridge

/-- If every member meets at least54 members, all supported points have degree
at least17. The bound uses disjoint neighborhoods in the actual point link. -/
theorem all_meeting_fifty_four_min_degree_seventeen
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (hm : ∀ R ∈ F, 54 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card)
    (x : α) (hx : x ∈ support F) : 17 ≤ degree F x := by
  classical
  by_contra hn
  have hd : degree F x ≤ 16 := by omega
  let G := residualLink F {x}
  have hGu : ∀ A ∈ G, A.card = 3 := by
    simpa [G] using residualLink_uniform (core := {x}) hu
  have hGf : IsSunflowerFree G 3 := residualLink_sunflowerFree hf
  have hGc : G.card = degree F x := by simp [G,card_residualLink,upperStar,degree]
  obtain ⟨R,hR,hxR⟩ := Finset.mem_biUnion.mp hx
  have hxR' : x ∈ R := hxR
  have hne : G.Nonempty := ⟨R \ {x},mem_residualLink_iff.mpr ⟨R,hR,by simpa,rfl⟩⟩
  have hmin : ∀ A ∈ G, 9 ≤ (exactTrace G A ∅).card := by
    intro A hA
    obtain ⟨S,hS,hxS,hSA⟩ := mem_residualLink_iff.mp hA
    have hxS' : x ∈ S := hxS (by simp)
    have hscore := meeting_at_least_fifty_four_degree_trace_score F hu hf S hS
      (hm S hS) x hxS'
    have he : (exactTrace G A ∅).card = (exactTrace F S {x}).card := by
      rw [← hSA]
      change (exactTrace (residualLink F {x}) (S \ {x}) ∅).card = _
      rw [← singleton_residual_eq_empty_link_trace F S x hxS',exact_trace_card_residual]
    rw [he]
    omega
  have hbound := twice_min_disjoint_degree_le_card G 9 hne (by decide)
    (fun A hA => Finset.card_pos.mp (by rw [hGu A hA]; decide)) hGf hmin
  omega

end Erdos20V10MinimumDegree
