import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace FrontierSupportGrid

/-- A finite integer bound used in the top-three-star support calculation.
This is only the numerical leaf; its semantic combinatorial hypotheses are
separate obligations. -/
def GridBound (a b c : ℕ) : Prop :=
  1 ≤ c → c ≤ b → b ≤ a → a + b ≤ 34 → a + b + c ≤ 46 →
  let A : ℤ := a
  let B : ℤ := b
  let C : ℤ := c
  let L : ℤ := max 0 (A + B + C - 28)
  3 * (55 * C + (A - C) * (A - 1) + (B - C) * (B - 1))
    - L * L + 3 * L ≤ 2250

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem grid_bound : ∀ a b c : Fin 20, GridBound a.val b.val c.val := by
  unfold GridBound
  decide

theorem natural_grid_bound (a b c : ℕ) (ha : a ≤ 19) (hb : b ≤ a) (hc : c ≤ b) :
    GridBound a b c := by
  exact grid_bound ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩

end FrontierSupportGrid

#print axioms FrontierSupportGrid.grid_bound
#print axioms FrontierSupportGrid.natural_grid_bound
