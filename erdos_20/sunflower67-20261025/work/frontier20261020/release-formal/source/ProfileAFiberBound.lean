import HeavyExtensionPairs
import ProfileACounts

namespace FrontierProfileAFiberBound
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence Erdos20CrossBounds
open FrontierHeavyExtensionPairs FrontierExtensionPairs

/-- A sunflower-free graph supported on four points has at most four edges. -/
theorem two_uniform_four_support_card_le_four
    {α : Type*} [DecidableEq α] (G : Finset (Finset α)) (O : Finset α)
    (hu : ∀ Q ∈ G, Q.card = 2) (hf : IsSunflowerFree G 3)
    (hs : ∀ Q ∈ G, Q ⊆ O) (hO : O.card = 4) : G.card ≤ 4 := by
  have hi := incidence_sum_eq G O
  have hl : (∑ Q ∈ G, (Q ∩ O).card) = G.card * 2 := by
    calc
      _ = ∑ _Q ∈ G, 2 := Finset.sum_congr rfl (fun Q hQ => by rw [Finset.inter_eq_left.mpr (hs Q hQ),hu Q hQ])
      _ = _ := by simp
  have hr : (∑ v ∈ O, (G.filter (fun Q => v ∈ Q)).card) ≤ 8 := by
    calc
      _ ≤ ∑ _v ∈ O, 2 := Finset.sum_le_sum (fun v _ => rank_two_three_petals_degree_le_two G hu hf v)
      _ = 8 := by simp [hO]
  omega

/-- Fixing the two design-side points leaves at most four choices of the
outside pair. This statement refers to actual original four-sets. -/
theorem fixed_pair_four_outsiders_card_le_four
    {α : Type*} [DecidableEq α] (G : Finset (Finset α)) (P O : Finset α)
    (hu : ∀ R ∈ G, R.card = 4) (hf : IsSunflowerFree G 3)
    (hP : P.card = 2) (hO : O.card = 4)
    (hc : ∀ R ∈ G, P ⊆ R) (hs : ∀ R ∈ G, R \ P ⊆ O) : G.card ≤ 4 := by
  have hl : (residualLink G P).card = G.card := by
    rw [card_residualLink]
    have he : upperStar G P = G := by
      apply Finset.filter_eq_self.mpr
      exact hc
    rw [he]
  have huL : ∀ Q ∈ residualLink G P, Q.card = 2 := by
    simpa [hP] using residualLink_uniform (core := P) hu
  have hsL : ∀ Q ∈ residualLink G P, Q ⊆ O := by
    intro Q hQ
    obtain ⟨R,hR,hPR,rfl⟩ := mem_residualLink_iff.mp hQ
    exact hs R hR
  have hb := two_uniform_four_support_card_le_four (residualLink G P) O huL
    (residualLink_sunflowerFree hf) hsL hO
  simpa only [hl] using hb

/-- A family with heavy extension-pair keys and fibers of size at most four
has at most twenty members. All representation inputs are explicit. -/
theorem heavy_keys_four_fibers_card_le_twenty
    {β : Type*} [DecidableEq β] (G : Finset β) (key : β → Finset (Fin 6))
    (w : Fin 6 → ℕ)
    (hu : ∀ R ∈ G, (key R).card = 2)
    (hw : ∑ v, w v ≤ 10)
    (hh : ∀ R ∈ G, 9 ≤ ∑ v ∈ extensionPair (key R), w v)
    (hcap : ∀ P ∈ G.image key, (G.filter (fun R => key R = P)).card ≤ 4) :
    G.card ≤ 20 := by
  let K := G.image key
  have hKu : ∀ P ∈ K, P.card = 2 := by
    intro P hP
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hP
    exact hu R hR
  have hKh : ∀ P ∈ K, 9 ≤ ∑ v ∈ extensionPair P, w v := by
    intro P hP
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hP
    exact hh R hR
  have hKcard := heavy_extension_pairs_card_le_five K w hKu hw hKh
  have hcover : G ⊆ K.biUnion (fun P => G.filter (fun R => key R = P)) := by
    intro R hR
    exact Finset.mem_biUnion.mpr ⟨key R,Finset.mem_image.mpr ⟨R,hR,rfl⟩,Finset.mem_filter.mpr ⟨hR,rfl⟩⟩
  calc
    G.card ≤ (K.biUnion (fun P => G.filter (fun R => key R = P))).card := Finset.card_le_card hcover
    _ ≤ ∑ P ∈ K, (G.filter (fun R => key R = P)).card := Finset.card_biUnion_le
    _ ≤ ∑ _P ∈ K, 4 := Finset.sum_le_sum (fun P hP => hcap P hP)
    _ = K.card * 4 := by simp
    _ ≤ 20 := by omega

/-- Terminal arithmetic/counting assembly. The key and weight bridges must
still be supplied by actual-family geometry; they are not axioms. -/
theorem profile_a_impossible_of_heavy_key_geometry
    {α : Type} [DecidableEq α]
    (M : FrontierProfileACounts.ResidualProfileA α)
    (hI : Erdos20V8Targets.IntersectingRankFourUpper 27)
    (key : Finset α → Finset (Fin 6)) (w : Fin 6 → ℕ)
    (hu : ∀ R ∈ M.rows 2, (key R).card = 2)
    (hw : ∑ v, w v ≤ 10)
    (hh : ∀ R ∈ M.rows 2, 9 ≤ ∑ v ∈ extensionPair (key R), w v)
    (hcap : ∀ P ∈ (M.rows 2).image key,
      ((M.rows 2).filter (fun R => key R = P)).card ≤ 4) : False := by
  have hlo := (M.final_count_window hI).2.2.1
  have hhi := heavy_keys_four_fibers_card_le_twenty (M.rows 2) key w hu hw hh hcap
  omega

end FrontierProfileAFiberBound
