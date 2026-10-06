import SunflowerLean.Erdos20Frontier

-- Intended negative test: dropping positive rank permits this false endpoint.
example : ({∅} : Finset (Finset (Fin 1))).card > (2 : ℕ)^0 := by decide
