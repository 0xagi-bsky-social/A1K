import SunflowerLean.Erdos20V13Trace

-- The displayed score-26 relaxation has total score 110 and M=54, T=0.
example : (18+19+19+19)+(8+9+9+9) = (110 : ℕ) := by decide
-- Intended rejection: the exact trace identity has constant +2, not +1.
theorem wrong_trace_identity_constant :
    (18+19+19+19)+(8+9+9+9) = (2*54+1+0 : ℕ) := by decide
