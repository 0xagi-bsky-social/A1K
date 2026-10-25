import SunflowerLean.Erdos20Endpoints

/-! Small kernel-checked obstructions to overstrong parameter choices.
Finite checks use `decide`, not externally executed decision procedures. -/
namespace Erdos20Obstructions

open Erdos20BCWConditional Erdos20Endpoints

def cycleFive : Finset (Finset (Fin 5)) :=
  {{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 0}}

def completeFive : Finset (Finset (Fin 5)) :=
  (Finset.univ : Finset (Fin 5)).powersetCard 2

theorem cycleFive_card : cycleFive.card = 5 := by decide

theorem cycleFive_uniform : ∀ S ∈ cycleFive, S.card = 2 := by decide

theorem cycleFive_strict_spread :
    ∀ Z : Finset (Fin 5), Z.Nonempty →
      (cycleFive.filter (fun S => Z ⊆ S)).card * 2 ^ Z.card <
        cycleFive.card := by decide

theorem cycleFive_spread : IsRSpread cycleFive 2 := by
  constructor
  · decide
  constructor
  · decide
  intro Z
  by_cases hZ : Z.Nonempty
  · exact Nat.le_of_lt (cycleFive_strict_spread Z hZ)
  · have he : Z = ∅ := Finset.not_nonempty_iff_eq_empty.mp hZ
    simp [he]

private theorem cycleFive_no_sunflower_triple :
    ∀ S ∈ cycleFive, ∀ T ∈ cycleFive, ∀ U ∈ cycleFive,
    S ≠ T → S ≠ U → T ≠ U →
      ¬ (S ∩ T = S ∩ U ∧ S ∩ T = T ∩ U) := by decide

theorem cycleFive_sunflower_free : IsSunflowerFree cycleFive 3 := by
  intro family hsub hsun
  obtain ⟨S, T, U, hST, hSU, hTU, hfamily⟩ :=
    Finset.card_eq_three.mp hsun.1
  have hS : S ∈ family := by simp [hfamily]
  have hT : T ∈ family := by simp [hfamily]
  have hU : U ∈ family := by simp [hfamily]
  obtain ⟨core, hcore⟩ := hsun.2
  apply cycleFive_no_sunflower_triple S (hsub hS) T (hsub hT) U
    (hsub hU) hST hSU hTU
  exact ⟨(hcore S T hS hT hST).trans (hcore S U hS hU hSU).symm,
    (hcore S T hS hT hST).trans (hcore T U hT hU hTU).symm⟩

theorem not_uniformExtremalBound_two_three :
    ¬ UniformExtremalBound.{0} 2 3 := by
  intro h
  have hb := h cycleFive 2 cycleFive_uniform cycleFive_sunflower_free
  rw [cycleFive_card] at hb
  norm_num at hb

theorem not_directSpreadMatching_two_three :
    ¬ DirectSpreadMatching.{0} 2 3 := by
  intro h
  obtain ⟨matching, hsub, hcard, hdis⟩ :=
    h cycleFive 2 cycleFive_uniform cycleFive_spread (by
      rw [cycleFive_card]; norm_num)
  exact cycleFive_sunflower_free matching hsub
    (disjoint_is_sunflower matching 3 hcard hdis)

/-- Disjoint rank-m sets use exactly m times as many ground elements. -/
theorem matching_size_times_rank_le_ground {n m : ℕ}
    (matching : Finset (Finset (Fin n)))
    (huniform : ∀ S ∈ matching, S.card = m)
    (hdis : IsPairwiseDisjoint matching) :
    matching.card * m ≤ n := by
  have hpair : (matching : Set (Finset (Fin n))).PairwiseDisjoint id := by
    intro S hS T hT hne
    exact Finset.disjoint_iff_inter_eq_empty.mpr (hdis S T hS hT hne)
  have hcount : (matching.biUnion id).card = matching.card * m := by
    rw [Finset.card_biUnion hpair]
    simp only [id_eq]
    rw [Finset.sum_congr rfl (fun S hS => huniform S hS)]
    simp
  have hle := Finset.card_le_card
    (Finset.subset_univ (matching.biUnion id))
  simpa [hcount] using hle

theorem completeFive_card : completeFive.card = 10 := by decide

theorem completeFive_uniform : ∀ S ∈ completeFive, S.card = 2 := by
  intro S hS
  exact (Finset.mem_powersetCard.mp hS).2

theorem completeFive_strict_spread :
    ∀ Z : Finset (Fin 5), Z.Nonempty →
      (completeFive.filter (fun S => Z ⊆ S)).card * 2 ^ Z.card <
        completeFive.card := by decide

theorem completeFive_has_no_three_matching :
    ¬ ∃ matching : Finset (Finset (Fin 5)),
      matching ⊆ completeFive ∧ matching.card = 3 ∧
        IsPairwiseDisjoint matching := by
  rintro ⟨matching, hsub, hcard, hdis⟩
  have hb := matching_size_times_rank_le_ground matching
    (fun S hS => completeFive_uniform S (hsub hS)) hdis
  rw [hcard] at hb
  norm_num at hb

/-- This particular strict-spread family already contains a sunflower,
although it has no three disjoint members. -/
theorem completeFive_has_sunflower :
    ∃ family, family ⊆ completeFive ∧ IsSunflower family 3 := by
  refine ⟨{{0, 1}, {0, 2}, {0, 3}}, ?_, ?_⟩
  · decide
  refine ⟨by decide, {0}, ?_⟩
  decide

end Erdos20Obstructions

#print axioms Erdos20Obstructions.cycleFive_strict_spread
#print axioms Erdos20Obstructions.cycleFive_sunflower_free
#print axioms Erdos20Obstructions.not_uniformExtremalBound_two_three
#print axioms Erdos20Obstructions.not_directSpreadMatching_two_three
#print axioms Erdos20Obstructions.matching_size_times_rank_le_ground
#print axioms Erdos20Obstructions.completeFive_strict_spread
#print axioms Erdos20Obstructions.completeFive_has_no_three_matching
#print axioms Erdos20Obstructions.completeFive_has_sunflower
