import SupportReduction

/-! Literal statement-fidelity tests. The four theorems below remove the public
predicate aliases, including the sunflower definition, from the claim interface.
An empty core is permitted; distinctness is required for the sunflower's members.
The intersecting premise includes S = T, exactly as in the public roots. -/

namespace FrontierLiteralStatements
universe u

theorem literal_support56 {α : Type u} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4)
    (hf : ∀ H : Finset (Finset α), H ⊆ F →
      ¬(H.card = 3 ∧ ∃ core : Finset α,
        ∀ S T : Finset α, S ∈ H → T ∈ H → S ≠ T → S ∩ T = core))
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 28) :
    (F.biUnion id).card ≤ 56 := by
  exact FrontierSupportFinish.intersecting_twenty_eight_support_le_fifty_six
    F hu hf hi hc

theorem literal_support53 {α : Type u} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4)
    (hf : ∀ H : Finset (Finset α), H ⊆ F →
      ¬(H.card = 3 ∧ ∃ core : Finset α,
        ∀ S T : Finset α, S ∈ H → T ∈ H → S ≠ T → S ∩ T = core))
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 28) :
    (F.biUnion id).card ≤ 53 := by
  exact FrontierSupportFinish.intersecting_twenty_eight_support_le_fifty_three
    F hu hf hi hc

theorem literal_i27_iff_no_fin56 :
    (∀ {α : Type} [DecidableEq α] (F : Finset (Finset α)),
      (∀ S ∈ F, S.card = 4) →
      (∀ H : Finset (Finset α), H ⊆ F →
        ¬(H.card = 3 ∧ ∃ core : Finset α,
          ∀ S T : Finset α, S ∈ H → T ∈ H → S ≠ T → S ∩ T = core)) →
      (∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) → F.card ≤ 27) ↔
    ¬(∃ G : Finset (Finset (Fin 56)), G.card = 28 ∧
      (∀ S ∈ G, S.card = 4) ∧
      (∀ H : Finset (Finset (Fin 56)), H ⊆ G →
        ¬(H.card = 3 ∧ ∃ core : Finset (Fin 56),
          ∀ S T : Finset (Fin 56), S ∈ H → T ∈ H → S ≠ T → S ∩ T = core)) ∧
      (∀ S ∈ G, ∀ T ∈ G, (S ∩ T).Nonempty)) := by
  exact FrontierSupportReduction.intersecting_upper_twenty_seven_iff_no_finite56_obstruction

theorem literal_i27_iff_no_fin53 :
    (∀ {α : Type} [DecidableEq α] (F : Finset (Finset α)),
      (∀ S ∈ F, S.card = 4) →
      (∀ H : Finset (Finset α), H ⊆ F →
        ¬(H.card = 3 ∧ ∃ core : Finset α,
          ∀ S T : Finset α, S ∈ H → T ∈ H → S ≠ T → S ∩ T = core)) →
      (∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) → F.card ≤ 27) ↔
    ¬(∃ G : Finset (Finset (Fin 53)), G.card = 28 ∧
      (∀ S ∈ G, S.card = 4) ∧
      (∀ H : Finset (Finset (Fin 53)), H ⊆ G →
        ¬(H.card = 3 ∧ ∃ core : Finset (Fin 53),
          ∀ S T : Finset (Fin 53), S ∈ H → T ∈ H → S ≠ T → S ∩ T = core)) ∧
      (∀ S ∈ G, ∀ T ∈ G, (S ∩ T).Nonempty)) := by
  exact FrontierSupportReduction.intersecting_upper_twenty_seven_iff_no_finite53_obstruction

end FrontierLiteralStatements

#print axioms FrontierLiteralStatements.literal_support56
#print axioms FrontierLiteralStatements.literal_support53
#print axioms FrontierLiteralStatements.literal_i27_iff_no_fin56
#print axioms FrontierLiteralStatements.literal_i27_iff_no_fin53
