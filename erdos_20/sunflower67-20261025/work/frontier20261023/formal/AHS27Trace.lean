import AHS27Data
namespace FrontierAHS27
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
/-- The exact finite isolation fact, including traces with fewer than four points. -/
theorem trace_blockers (T : Finset (Fin 9))
    (hne : T.Nonempty) (hcard : T.card ≤ 4) (hout : T ∉ AHS) :
    ∃ A ∈ AHS, ∃ B ∈ AHS, A ≠ B ∧
      A ∩ B = A ∩ T ∧ A ∩ B = B ∩ T := by
  have h : ∀ T : Finset (Fin 9), T.Nonempty → T.card ≤ 4 → T ∉ AHS →
      ∃ A ∈ AHS, ∃ B ∈ AHS, A ≠ B ∧
        A ∩ B = A ∩ T ∧ A ∩ B = B ∩ T := by
    decide +kernel
  exact h T hne hcard hout

end FrontierAHS27
