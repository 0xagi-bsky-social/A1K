import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace FrontierSupportGrid53

/-- Numerical leaf only; the four-star semantic argument is separate. -/
def GridBound (a b c d : ℕ) : Prop :=
  1 ≤ d → d ≤ c → c ≤ b → b ≤ a → a+b ≤ 34 → a+b+c ≤ 46 → a+b+c+d ≤ 60 →
  let A : ℤ := a
  let B : ℤ := b
  let C : ℤ := c
  let D : ℤ := d
  let L : ℤ := max 0 (A+B+C+D-28)
  6*(58*D+(A-D)*(A-1)+(B-D)*(B-1)+(C-D)*(C-1))-L*L+6*L ≤ 4475

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem grid_bound : ∀ a : Fin 20, ∀ b : Fin (a.val+1), ∀ c : Fin (b.val+1),
    ∀ d : Fin (c.val+1), GridBound a.val b.val c.val d.val := by
  unfold GridBound
  decide

theorem natural_grid_bound (a b c d : ℕ) (ha : a≤19) (hb : b≤a) (hc : c≤b) (hd : d≤c) :
    GridBound a b c d := by
  exact grid_bound ⟨a,by omega⟩ ⟨b,by change b<a+1; omega⟩
    ⟨c,by change c<b+1; omega⟩ ⟨d,by change d<c+1; omega⟩

end FrontierSupportGrid53
#print axioms FrontierSupportGrid53.grid_bound
#print axioms FrontierSupportGrid53.natural_grid_bound
