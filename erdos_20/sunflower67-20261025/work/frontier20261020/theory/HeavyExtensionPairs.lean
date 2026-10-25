import ExtensionPairs

namespace FrontierHeavyExtensionPairs
open FrontierExtensionPairs

set_option maxRecDepth 10000 in
/-- Exactly five two-element subsets of a six-point set contain a fixed point. -/
theorem five_pairs_at_point :
    ∀ v : Fin 6,
      ((Finset.univ.powersetCard 2).filter (fun P : Finset (Fin 6) => v ∈ P)).card = 5 := by
  decide

/-- A nine-of-ten weight condition forces all eligible pairs through one
point. This is stronger than merely asserting pairwise intersection. -/
theorem heavy_pairs_common_point
    (Q : Finset (Finset (Fin 6))) (w : Fin 6 → ℕ)
    (hQ : Q.Nonempty) (hu : ∀ P ∈ Q, P.card = 2)
    (hw : ∑ v, w v ≤ 10) (hh : ∀ P ∈ Q, 9 ≤ ∑ v ∈ P, w v) :
    ∃ a : Fin 6, ∀ P ∈ Q, a ∈ P := by
  obtain ⟨P,hP⟩ := hQ
  obtain ⟨a,b,hab,hshape⟩ := Finset.card_eq_two.mp (hu P hP)
  have hweight := hh P hP
  rw [hshape] at hweight
  simp only [Finset.sum_pair hab] at hweight
  have choose_point (a : Fin 6) (ha : 5 ≤ w a) : ∀ P ∈ Q, a ∈ P := by
    intro P hP
    by_contra han
    have hsum : (∑ v ∈ insert a P, w v) ≤ ∑ v : Fin 6, w v :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; omega)
    rw [Finset.sum_insert han] at hsum
    have hp := hh P hP
    omega
  by_cases ha : 5 ≤ w a
  · exact ⟨a,choose_point a ha⟩
  · have hb : 5 ≤ w b := by omega
    exact ⟨b,choose_point b hb⟩

/-- At most five distinct pairs can each capture nine of ten units of mass. -/
theorem heavy_pairs_card_le_five
    (Q : Finset (Finset (Fin 6))) (w : Fin 6 → ℕ)
    (hu : ∀ P ∈ Q, P.card = 2)
    (hw : ∑ v, w v ≤ 10) (hh : ∀ P ∈ Q, 9 ≤ ∑ v ∈ P, w v) :
    Q.card ≤ 5 := by
  by_cases hn : Q.Nonempty
  · obtain ⟨a,ha⟩ := heavy_pairs_common_point Q w hn hu hw hh
    have hsub : Q ⊆ (Finset.univ.powersetCard 2).filter (fun P => a ∈ P) := by
      intro P hP
      exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hu P hP⟩,ha P hP⟩
    have hb := Finset.card_le_card hsub
    simpa only [five_pairs_at_point a] using hb
  · have he : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he]

/-- The injective extension-pair map transfers the heavy-pair bound back to
used pairs of a canonical ten-triple design. -/
theorem heavy_extension_pairs_card_le_five
    (K : Finset (Finset (Fin 6))) (w : Fin 6 → ℕ)
    (hu : ∀ P ∈ K, P.card = 2)
    (hw : ∑ v, w v ≤ 10)
    (hh : ∀ P ∈ K, 9 ≤ ∑ v ∈ extensionPair P, w v) : K.card ≤ 5 := by
  have hu' : ∀ Q ∈ K.image extensionPair, Q.card = 2 := by
    intro Q hQ
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hQ
    exact extension_pair_card_two P (hu P hP)
  have hh' : ∀ Q ∈ K.image extensionPair, 9 ≤ ∑ v ∈ Q, w v := by
    intro Q hQ
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hQ
    exact hh P hP
  have hb := heavy_pairs_card_le_five (K.image extensionPair) w hu' hw hh'
  have hi : Set.InjOn extensionPair (↑K : Set (Finset (Fin 6))) := by
    intro P hP Q hQ he
    exact extension_pair_injective P Q (hu P hP) (hu Q hQ) he
  rw [Finset.card_image_of_injOn hi] at hb
  exact hb

end FrontierHeavyExtensionPairs
