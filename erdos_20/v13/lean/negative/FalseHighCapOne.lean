import SunflowerLean.Erdos20V9HighCompatibilityWitness
open Erdos20V9HighCompatibilityWitness Erdos20V8Boundary
example : (anchor ∩ highPoints family).card ≤ 1 := by
  rw [anchor_high_count_two]
  decide
