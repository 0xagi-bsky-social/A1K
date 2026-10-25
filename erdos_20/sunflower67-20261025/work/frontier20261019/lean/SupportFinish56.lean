import SupportFacts
import DegreeEnvelope
import MomentArithmetic

namespace FrontierSupportFinish
open Erdos20BCWConditional Erdos20DegreeCongruences
open FrontierSupport56 FrontierSupportFacts FrontierDegreeEnvelope FrontierMomentArithmetic
universe u

/-- Actual support bound for every hypothetical 28-member intersecting rank-four
three-sunflower-free family, with no bound on its ambient universe. -/
theorem intersecting_twenty_eight_support_le_fifty_six
    {α : Type u} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S∈F, S.card=4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S∈F, ∀ T∈F, (S∩T).Nonempty) (hc : F.card=28) :
    (support F).card ≤ 56 := by
  classical
  by_contra hnot
  have hn : 57 ≤ (support F).card := by omega
  have hnZ : (57 : ℤ) ≤ (support F).card := by exact_mod_cast hn
  have hd : ∀ x, degree F x ≤ 19 :=
    Erdos20ExtremalTransversals.intersecting_rank_four_card_ge_twenty_one_degree_le_nineteen
      F hu hf hi (by omega)
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz,hzy,hyx,htail⟩ :=
    exists_top_three (support F) (degree F) (by omega)
  let Q : ℤ := ∑ v∈support F, (degree F v : ℤ)^2
  let L : ℤ := max 0 ((degree F x : ℤ)+degree F y+degree F z-28)
  let X : ℤ := (F.filter (fun S => ({x,y} : Finset α) ⊆ S)).card
  let Y : ℤ := (F.filter (fun S => ({x,z} : Finset α) ⊆ S)).card
  let Z : ℤ := (F.filter (fun S => ({y,z} : Finset α) ⊆ S)).card
  let T : ℤ := (F.filter (fun S => ({x,y,z} : Finset α) ⊆ S)).card
  have htotal := degree_sum_twenty_eight F hu hc
  have henv := envelope_three (support F) (degree F) x y z hx hy hxy
    (degree_pos F) htail
  rw [quadratic_sum_eq, htotal] at henv
  have htailBudget := mul_nonneg (Int.natCast_nonneg (degree F z)) (sub_nonneg.mpr hnZ)
  have hupper : Q-112 ≤ 55*(degree F z : ℤ) +
      ((degree F x : ℤ)-degree F z)*((degree F x : ℤ)-1) +
      ((degree F y : ℤ)-degree F z)*((degree F y : ℤ)-1) := by
    dsimp [Q]
    nlinarith only [henv,htailBudget]
  have hm := three_star_second_moment F 4 x y z hxy hxz hyz hu hi
  dsimp only at hm
  rw [hc] at hm
  norm_num at hm
  have hLS : L ≤ X+Y+Z := by
    apply max_le
    · dsimp [X,Y,Z]; positivity
    · have hs := three_star_sum_bound F x y z hc
      dsimp [X,Y,Z]
      linarith
  have hlow := three_pair_moment_bound Q L X Y Z T (le_max_left _ _) hLS
    (by dsimp [X]; positivity) (by dsimp [Y]; positivity)
    (by dsimp [Z]; positivity) (by dsimp [T]; positivity)
    (triple_bound F hu hf x y z hxy hxz hyz)
    (by dsimp [Q,X,Y,Z,T]; linarith only [hm])
  have hg := FrontierSupportGrid.natural_grid_bound (degree F x) (degree F y)
    (degree F z) (hd x) hyx hzy (degree_pos F z hz) hzy hyx
    (two_degree_bound F hu hf hc x y hxy)
    (three_degree_bound F hu hf hc x y z hxy hxz hyz)
  change 3*(55*(degree F z : ℤ)+
    ((degree F x : ℤ)-degree F z)*((degree F x : ℤ)-1)+
    ((degree F y : ℤ)-degree F z)*((degree F y : ℤ)-1))-L*L+3*L≤2250 at hg
  nlinarith only [hupper,hlow,hg]

end FrontierSupportFinish
#print axioms FrontierSupportFinish.intersecting_twenty_eight_support_le_fifty_six
