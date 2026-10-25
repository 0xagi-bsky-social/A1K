import ProfileAFiberBound
import ProfileACounts

namespace FrontierProfileAFibers
open Erdos20BCWConditional Erdos20StrictCore
open FrontierProfileACounts FrontierProfileAFiberBound

variable {α : Type} [DecidableEq α] (M : ResidualProfileA α)

/-- The actual design-side pair of a residual row having two outsiders. -/
def key (R : Finset α) : Finset α := R \ M.O

theorem row_key_card_two (R : Finset α) (hR : R ∈ M.rows 2) :
    (key M R).card = 2 := by
  obtain ⟨hRH,hR2⟩ := Finset.mem_filter.mp hR
  have h := Finset.card_sdiff_add_card_inter R M.O
  rw [M.uniform_H R hRH,hR2] at h
  change (R \ M.O).card = 2
  omega

theorem key_card_two (P : Finset α) (hP : P ∈ (M.rows 2).image (key M)) :
    P.card = 2 := by
  obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hP
  exact row_key_card_two M R hR

theorem fiber_card_le_four (P : Finset α) (hP : P ∈ (M.rows 2).image (key M)) :
    ((M.rows 2).filter (fun R => key M R = P)).card ≤ 4 := by
  let G := (M.rows 2).filter (fun R => key M R = P)
  have hGH : G ⊆ M.H := by
    intro R hR
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1
  apply fixed_pair_four_outsiders_card_le_four G P M.O
  · exact fun R hR => M.uniform_H R (hGH hR)
  · exact fun K hK hsun => M.free_H K (hK.trans hGH) hsun
  · exact key_card_two M P hP
  · exact M.outsiders_card
  · intro R hR
    have he := (Finset.mem_filter.mp hR).2
    rw [← he]
    exact Finset.sdiff_subset
  · intro R hR v hv
    obtain ⟨hvR,hvP⟩ := Finset.mem_sdiff.mp hv
    have he : R \ M.O = P := (Finset.mem_filter.mp hR).2
    by_contra hn
    exact hvP (he ▸ Finset.mem_sdiff.mpr ⟨hvR,hn⟩)

theorem rows_card_le_four_mul_keys :
    (M.rows 2).card ≤ 4 * ((M.rows 2).image (key M)).card := by
  let G := M.rows 2
  let K := G.image (key M)
  have hcover : G ⊆ K.biUnion (fun P => G.filter (fun R => key M R = P)) := by
    intro R hR
    exact Finset.mem_biUnion.mpr ⟨key M R,Finset.mem_image.mpr ⟨R,hR,rfl⟩,
      Finset.mem_filter.mpr ⟨hR,rfl⟩⟩
  calc
    G.card ≤ (K.biUnion (fun P => G.filter (fun R => key M R = P))).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ P ∈ K, (G.filter (fun R => key M R = P)).card := Finset.card_biUnion_le
    _ ≤ ∑ _P ∈ K, 4 := Finset.sum_le_sum (fun P hP => fiber_card_le_four M P hP)
    _ = 4 * K.card := by simp [Nat.mul_comm]

end FrontierProfileAFibers
