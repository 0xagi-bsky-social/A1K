import SupportFacts
import DegreeEnvelope
import MomentArithmetic
import FourStar
import SupportGrid53

namespace FrontierSupportFinish
open Erdos20BCWConditional Erdos20DegreeCongruences
open FrontierSupportFacts FrontierDegreeEnvelope FrontierMomentArithmetic FrontierFourStar
universe u

/-- Four-star correction reduces the actual support to at most53, without
any restriction on the ambient universe and without assuming I27. -/
theorem intersecting_twenty_eight_support_le_fifty_three
    {α : Type u} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S∈F, S.card=4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S∈F, ∀ T∈F, (S∩T).Nonempty) (hc : F.card=28) :
    (support F).card ≤ 53 := by
  classical
  by_contra hnot
  have hn : 54 ≤ (support F).card := by omega
  have hnZ : (54 : ℤ) ≤ (support F).card := by exact_mod_cast hn
  have hd : ∀ x, degree F x ≤ 19 :=
    Erdos20ExtremalTransversals.intersecting_rank_four_card_ge_twenty_one_degree_le_nineteen
      F hu hf hi (by omega)
  obtain ⟨x,y,z,w,hx,hy,hz,hw,hxy,hxz,hxw,hyz,hyw,hzw,hwz,hzy,hyx,htail⟩ :=
    exists_top_four (support F) (degree F) (by omega)
  let Q : ℤ := ∑ v∈support F, (degree F v : ℤ)^2
  let L : ℤ := max 0 ((degree F x : ℤ)+degree F y+degree F z+degree F w-28)
  let X₁ : ℤ := (F.filter (fun S => ({x,y} : Finset α) ⊆ S)).card
  let X₂ : ℤ := (F.filter (fun S => ({x,z} : Finset α) ⊆ S)).card
  let X₃ : ℤ := (F.filter (fun S => ({x,w} : Finset α) ⊆ S)).card
  let X₄ : ℤ := (F.filter (fun S => ({y,z} : Finset α) ⊆ S)).card
  let X₅ : ℤ := (F.filter (fun S => ({y,w} : Finset α) ⊆ S)).card
  let X₆ : ℤ := (F.filter (fun S => ({z,w} : Finset α) ⊆ S)).card
  let T₁ : ℤ := (F.filter (fun S => ({x,y,z} : Finset α) ⊆ S)).card
  let T₂ : ℤ := (F.filter (fun S => ({x,y,w} : Finset α) ⊆ S)).card
  let T₃ : ℤ := (F.filter (fun S => ({x,z,w} : Finset α) ⊆ S)).card
  let T₄ : ℤ := (F.filter (fun S => ({y,z,w} : Finset α) ⊆ S)).card
  have htotal := degree_sum_twenty_eight F hu hc
  have henv := envelope_four (support F) (degree F) x y z w hx hy hz hxy hxz hyz
    (degree_pos F) htail
  rw [quadratic_sum_eq, htotal] at henv
  have htailBudget := mul_nonneg (Int.natCast_nonneg (degree F w)) (sub_nonneg.mpr hnZ)
  have hupper : Q-112 ≤ 58*(degree F w : ℤ) +
      ((degree F x : ℤ)-degree F w)*((degree F x : ℤ)-1) +
      ((degree F y : ℤ)-degree F w)*((degree F y : ℤ)-1) +
      ((degree F z : ℤ)-degree F w)*((degree F z : ℤ)-1) := by
    dsimp [Q]
    nlinarith only [henv,htailBudget]
  have hm := four_star_second_moment F 4 x y z w hxy hxz hxw hyz hyw hzw hu hi
  dsimp only at hm
  rw [hc] at hm
  norm_num at hm
  have hLS : L ≤ X₁+X₂+X₃+X₄+X₅+X₆ := by
    apply max_le
    · dsimp [X₁,X₂,X₃,X₄,X₅,X₆]; positivity
    · have hs := four_star_sum_bound F x y z w hc
      dsimp [X₁,X₂,X₃,X₄,X₅,X₆]
      linarith
  have hlow := six_pair_moment_bound Q L X₁ X₂ X₃ X₄ X₅ X₆ T₁ T₂ T₃ T₄
    (le_max_left _ _) hLS
    (by dsimp [X₁]; positivity) (by dsimp [X₂]; positivity)
    (by dsimp [X₃]; positivity) (by dsimp [X₄]; positivity)
    (by dsimp [X₅]; positivity) (by dsimp [X₆]; positivity)
    (by dsimp [T₁]; positivity) (triple_bound F hu hf x y z hxy hxz hyz)
    (by dsimp [T₂]; positivity) (triple_bound F hu hf x y w hxy hxw hyw)
    (by dsimp [T₃]; positivity) (triple_bound F hu hf x z w hxz hxw hzw)
    (by dsimp [T₄]; positivity) (triple_bound F hu hf y z w hyz hyw hzw)
    (by dsimp [Q,X₁,X₂,X₃,X₄,X₅,X₆,T₁,T₂,T₃,T₄]; linarith only [hm])
  have hfourZ := four_degree_sum_le_sixty F x y z w hxy hxz hxw hyz hyw hzw hu hf hc
  have hfour : degree F x+degree F y+degree F z+degree F w≤60 := by
    exact_mod_cast hfourZ
  have hg := FrontierSupportGrid53.natural_grid_bound (degree F x) (degree F y)
    (degree F z) (degree F w) (hd x) hyx hzy hwz
    (degree_pos F w hw) hwz hzy hyx
    (two_degree_bound F hu hf hc x y hxy)
    (three_degree_bound F hu hf hc x y z hxy hxz hyz) hfour
  change 6*(58*(degree F w : ℤ)+
    ((degree F x : ℤ)-degree F w)*((degree F x : ℤ)-1)+
    ((degree F y : ℤ)-degree F w)*((degree F y : ℤ)-1)+
    ((degree F z : ℤ)-degree F w)*((degree F z : ℤ)-1))-L*L+6*L≤4475 at hg
  nlinarith only [hupper,hlow,hg]

end FrontierSupportFinish
#print axioms FrontierSupportFinish.intersecting_twenty_eight_support_le_fifty_three
