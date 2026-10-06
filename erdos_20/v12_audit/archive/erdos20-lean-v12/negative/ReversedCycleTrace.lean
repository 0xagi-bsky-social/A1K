import SunflowerLean.Erdos20V11EdgePairs
open Erdos20V11EdgePairs
-- Intentionally false: reversing the cycle/noncycle sign destroys the certificate.
example : ∀ (a : Fin 6) (T : Finset (Fin 6)), a ∉ T → insert a T ∈ D →
    ∃ P ∈ D, ∃ Q ∈ D,
      a ∉ P ∧ a ∉ Q ∧ P ∩ T = P ∩ Q ∧ Q ∩ T = P ∩ Q := by
  decide +kernel
