import SunflowerLean.Erdos20V9HighCompatibilityWitness
open Erdos20BCWConditional Erdos20V9HighCompatibilityWitness
-- This actual pair has only three extensions in the explicit 35-member family.
example : (upperStar family ({1,2} : Finset (Fin 13))).card = 3 := by decide
-- Intentionally false: the reserve-four geometric proposal overcounts this pair.
example : 4 ≤ (upperStar family ({1,2} : Finset (Fin 13))).card := by decide
