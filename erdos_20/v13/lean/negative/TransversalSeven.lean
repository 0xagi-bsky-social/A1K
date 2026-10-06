import SunflowerLean.Erdos20V13Endpoint

open Erdos20V13Endpoint
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
example : nineteenTriples.card = 19 := by decide
example : nineteenTriples.filter (fun S =>
    (S ∩ ({0,1,2,6,7,8} : Finset (Fin 12))).Nonempty) = nineteenTriples := by decide
-- Intended rejection: this actual 19-triple family's transversal has six points.
theorem wrong_transversal_lower_seven :
    7 ≤ ({0,1,2,6,7,8} : Finset (Fin 12)).card := by decide
