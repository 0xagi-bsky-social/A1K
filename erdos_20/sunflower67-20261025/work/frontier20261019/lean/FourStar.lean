import Support56

namespace FrontierFourStar
open Erdos20BCWConditional Erdos20DegreeCongruences FrontierSupport56

universe u

def corrected {α : Type u} [DecidableEq α] (x y z w : α) (S : Finset α) : ℤ :=
  (S.card : ℤ) - indicator {x,y} S - indicator {x,z} S - indicator {x,w} S -
    indicator {y,z} S - indicator {y,w} S - indicator {z,w} S +
    indicator {x,y,z} S + indicator {x,y,w} S + indicator {x,z,w} S +
    indicator {y,z,w} S

theorem corrected_nonempty {α : Type u} [DecidableEq α]
    (x y z w : α) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (S : Finset α) (hS : S.Nonempty) : 1 ≤ corrected x y z w S := by
  classical
  have hpos : (1 : ℤ) ≤ S.card := by exact_mod_cast hS.card_pos
  have hmin : ((({x,y,z,w} : Finset α).filter (fun a => a ∈ S)).card : ℤ) ≤ S.card := by
    exact_mod_cast Finset.card_le_card (show
      ({x,y,z,w} : Finset α).filter (fun a => a ∈ S) ⊆ S from
      fun a ha => (Finset.mem_filter.mp ha).2)
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;>
    by_cases hz : z ∈ S <;> by_cases hw : w ∈ S
  all_goals
    simp [corrected, indicator, Finset.insert_subset_iff, Finset.filter_insert,
      Finset.filter_singleton,
      hxy, hxz, hxw, hyz, hyw, hzw, hx, hy, hz, hw] at hmin ⊢
    omega

/-- The four-star correction keeps the diagonal exact and works for every
uniform intersecting family, with no sunflower-free assumption. -/
theorem four_star_second_moment {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (r : ℕ) (x y z w : α)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (hu : ∀ S ∈ F, S.card=r)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) :
    let M : ℤ := F.card
    let X₁ : ℤ := ((F.filter (fun S => ({x,y} : Finset α) ⊆ S)).card : ℤ)
    let X₂ : ℤ := ((F.filter (fun S => ({x,z} : Finset α) ⊆ S)).card : ℤ)
    let X₃ : ℤ := ((F.filter (fun S => ({x,w} : Finset α) ⊆ S)).card : ℤ)
    let X₄ : ℤ := ((F.filter (fun S => ({y,z} : Finset α) ⊆ S)).card : ℤ)
    let X₅ : ℤ := ((F.filter (fun S => ({y,w} : Finset α) ⊆ S)).card : ℤ)
    let X₆ : ℤ := ((F.filter (fun S => ({z,w} : Finset α) ⊆ S)).card : ℤ)
    let T₁ : ℤ := ((F.filter (fun S => ({x,y,z} : Finset α) ⊆ S)).card : ℤ)
    let T₂ : ℤ := ((F.filter (fun S => ({x,y,w} : Finset α) ⊆ S)).card : ℤ)
    let T₃ : ℤ := ((F.filter (fun S => ({x,z,w} : Finset α) ⊆ S)).card : ℤ)
    let T₄ : ℤ := ((F.filter (fun S => ({y,z,w} : Finset α) ⊆ S)).card : ℤ)
    M*(M+r-1) + X₁*(X₁-1) + X₂*(X₂-1) + X₃*(X₃-1) + X₄*(X₄-1) +
      X₅*(X₅-1) + X₆*(X₆-1) - T₁*(T₁-1) - T₂*(T₂-1) -
      T₃*(T₃-1) - T₄*(T₄-1) ≤
      ∑ v ∈ support F, (degree F v : ℤ)^2 := by
  classical
  have hh := double_sum_ge_diagonal F (fun S T => corrected x y z w (S ∩ T))
    F.card rfl (fun S hS T hT _ =>
      corrected_nonempty x y z w hxy hxz hxw hyz hyw hzw _ (hi S hS T hT))
  have hsum : (∑ S ∈ F, (S.card : ℤ)) = (F.card : ℤ)*r := by
    calc
      _ = ∑ _S ∈ F, (r : ℤ) :=
        Finset.sum_congr rfl (fun S hS => by rw [hu S hS])
      _ = _ := by simp
  simp only [Finset.inter_self, corrected, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, sum_indicator] at hh
  rw [hsum] at hh
  simp_rw [double_sum_indicator] at hh
  rw [double_sum_inter_eq] at hh
  dsimp only
  nlinarith only [hh]

theorem four_star_sum_bound {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (x y z w : α) (hc : F.card=28) :
    (degree F x : ℤ) + degree F y + degree F z + degree F w ≤ 28 +
      ((F.filter (fun S => ({x,y} : Finset α) ⊆ S)).card : ℤ) +
      ((F.filter (fun S => ({x,z} : Finset α) ⊆ S)).card : ℤ) +
      ((F.filter (fun S => ({x,w} : Finset α) ⊆ S)).card : ℤ) +
      ((F.filter (fun S => ({y,z} : Finset α) ⊆ S)).card : ℤ) +
      ((F.filter (fun S => ({y,w} : Finset α) ⊆ S)).card : ℤ) +
      ((F.filter (fun S => ({z,w} : Finset α) ⊆ S)).card : ℤ) := by
  classical
  have hrow (S : Finset α) :
      indicator {x} S + indicator {y} S + indicator {z} S + indicator {w} S ≤
      1 + indicator {x,y} S + indicator {x,z} S + indicator {x,w} S +
        indicator {y,z} S + indicator {y,w} S + indicator {z,w} S := by
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;>
      by_cases hz : z ∈ S <;> by_cases hw : w ∈ S <;>
      simp [indicator, Finset.insert_subset_iff, hx,hy,hz,hw]
  have hh := Finset.sum_le_sum (fun S (_ : S ∈ F) => hrow S)
  simpa [Finset.sum_add_distrib, sum_indicator, degree, hc] using hh

theorem four_star_twice_sum_bound {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (x y z w : α) (hc : F.card=28) :
    2 * ((degree F x : ℤ) + degree F y + degree F z + degree F w) ≤ 84 +
      ((F.filter (fun S => ({x,y} : Finset α) ⊆ S)).card : ℤ) +
      ((F.filter (fun S => ({x,z} : Finset α) ⊆ S)).card : ℤ) +
      ((F.filter (fun S => ({x,w} : Finset α) ⊆ S)).card : ℤ) +
      ((F.filter (fun S => ({y,z} : Finset α) ⊆ S)).card : ℤ) +
      ((F.filter (fun S => ({y,w} : Finset α) ⊆ S)).card : ℤ) +
      ((F.filter (fun S => ({z,w} : Finset α) ⊆ S)).card : ℤ) := by
  classical
  have hrow (S : Finset α) :
      2 * (indicator {x} S + indicator {y} S + indicator {z} S + indicator {w} S) ≤
      3 + indicator {x,y} S + indicator {x,z} S + indicator {x,w} S +
        indicator {y,z} S + indicator {y,w} S + indicator {z,w} S := by
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;>
      by_cases hz : z ∈ S <;> by_cases hw : w ∈ S <;>
      simp [indicator, Finset.insert_subset_iff, hx,hy,hz,hw]
  have hh := Finset.sum_le_sum (fun S (_ : S ∈ F) => hrow S)
  simpa [← Finset.mul_sum, Finset.sum_add_distrib, sum_indicator, degree, hc] using hh

theorem four_degree_sum_le_sixty {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (x y z w : α)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (hu : ∀ S ∈ F, S.card=4) (hf : IsSunflowerFree F 3) (hc : F.card=28) :
    (degree F x : ℤ) + degree F y + degree F z + degree F w ≤ 60 := by
  have hb (a b : α) (hab : a ≠ b) :
      ((F.filter (fun S => ({a,b} : Finset α) ⊆ S)).card : ℤ) ≤ 6 := by
    have hh := Erdos20V11Census.rank_four_pair_codegree_le_six F hu hf a b hab
    change (F.filter (fun S => ({a,b} : Finset α) ⊆ S)).card ≤ 6 at hh
    exact_mod_cast hh
  have hh := four_star_twice_sum_bound F x y z w hc
  have h₁ := hb x y hxy
  have h₂ := hb x z hxz
  have h₃ := hb x w hxw
  have h₄ := hb y z hyz
  have h₅ := hb y w hyw
  have h₆ := hb z w hzw
  omega

/-- Removing distinctness from the corrected-intersection statement is false. -/
example : ¬ (1 ≤ corrected (0 : ℕ) 0 0 0 {0}) := by
  norm_num [corrected, indicator]

/-- Removing the nonempty-intersection condition is also false. -/
example : ¬ (1 ≤ corrected (0 : ℕ) 1 2 3 ∅) := by
  norm_num [corrected, indicator]

end FrontierFourStar

#print axioms FrontierFourStar.corrected_nonempty
#print axioms FrontierFourStar.four_star_second_moment
#print axioms FrontierFourStar.four_star_sum_bound
#print axioms FrontierFourStar.four_star_twice_sum_bound
#print axioms FrontierFourStar.four_degree_sum_le_sixty
