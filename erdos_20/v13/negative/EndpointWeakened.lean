import SunflowerLean.Erdos20V13Endpoint

open Erdos20V13Endpoint Erdos20BCWConditional
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Intentionally false specialization of the improperly weakened conclusion.
theorem rejected_weakened_endpoint :
    ∃ y : Option (Fin 12), none ≠ y ∧ (upperStar family {none,y}).card=6 := by
  decide
