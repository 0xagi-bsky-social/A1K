import SunflowerLean.Erdos20Obstructions

-- Intended negative test: deliberately wrong finite-certificate cardinality.
example : Erdos20Obstructions.cycleFive.card = 4 := by decide
