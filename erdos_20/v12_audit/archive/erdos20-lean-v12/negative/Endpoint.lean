import SunflowerLean.Erdos20Frontier

-- Intended negative test: q+1 does not make the forcing endpoint strict at r=1.
example : (1 : ℕ)^1+1 < (1+1)^1 := by decide
