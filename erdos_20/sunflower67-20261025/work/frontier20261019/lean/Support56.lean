import SunflowerLean.Erdos20V13FiniteReduction
import SunflowerLean.Erdos20ExtremalTransversals
import SunflowerLean.Erdos20V11CensusCapacity
import SupportBound
import SupportGrid

namespace FrontierSupport56
open Erdos20BCWConditional Erdos20DegreeCongruences Erdos20Incidence

universe u

def indicator {α : Type u} [DecidableEq α] (C S : Finset α) : ℤ :=
  if C ⊆ S then 1 else 0

theorem sum_indicator {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (C : Finset α) :
    (∑ S ∈ F, indicator C S) = ((F.filter (fun S => C ⊆ S)).card : ℤ) := by
  classical
  have hh : (∑ S ∈ F, if C ⊆ S then (1 : ℕ) else 0) =
      (F.filter (fun S => C ⊆ S)).card := (Finset.card_filter _ _).symm
  unfold indicator
  exact_mod_cast hh

theorem indicator_inter {α : Type u} [DecidableEq α]
    (C S T : Finset α) : indicator C (S ∩ T) = indicator C S * indicator C T := by
  by_cases hS : C ⊆ S <;> by_cases hT : C ⊆ T <;>
    simp [indicator, Finset.subset_inter_iff, hS, hT]

theorem double_sum_indicator {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (C : Finset α) :
    (∑ S ∈ F, ∑ T ∈ F, indicator C (S ∩ T)) =
      ((F.filter (fun S => C ⊆ S)).card : ℤ)^2 := by
  classical
  simp_rw [indicator_inter]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, sum_indicator]
  ring

def corrected {α : Type u} [DecidableEq α] (x y z : α) (S : Finset α) : ℤ :=
  (S.card : ℤ) + indicator {x,y,z} S -
    indicator {x,y} S - indicator {x,z} S - indicator {y,z} S

theorem corrected_nonempty {α : Type u} [DecidableEq α]
    (x y z : α) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (S : Finset α) (hS : S.Nonempty) : 1 ≤ corrected x y z S := by
  classical
  have hpos : (1 : ℤ) ≤ S.card := by exact_mod_cast hS.card_pos
  have hp (C : Finset α) (hc : C ⊆ S) : (C.card : ℤ) ≤ S.card := by
    exact_mod_cast Finset.card_le_card hc
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> by_cases hz : z ∈ S
  all_goals
    simp only [corrected, indicator, Finset.insert_subset_iff,
      Finset.singleton_subset_iff, hx, hy, hz, and_self, and_true, and_false,
      true_and, false_and, if_true, if_false]
  · have hh := hp {x,y,z} (by
      simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
      exact ⟨hx,hy,hz⟩)
    norm_num [hxy,hxz,hyz] at hh
    omega
  · have hh := hp {x,y} (by
      simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
      exact ⟨hx,hy⟩)
    norm_num [hxy] at hh
    omega
  · have hh := hp {x,z} (by
      simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
      exact ⟨hx,hz⟩)
    norm_num [hxz] at hh
    omega
  · omega
  · have hh := hp {y,z} (by
      simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
      exact ⟨hy,hz⟩)
    norm_num [hyz] at hh
    omega
  · omega
  · omega
  · omega

/-- Generic ordered-pair lower bound with the diagonal retained exactly. -/
theorem double_sum_ge_diagonal {β : Type u} [DecidableEq β]
    (F : Finset β) (k : β → β → ℤ) (m : ℕ) (hc : F.card = m)
    (hk : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → 1 ≤ k S T) :
    (m : ℤ) * (m - 1) + ∑ S ∈ F, k S S ≤ ∑ S ∈ F, ∑ T ∈ F, k S T := by
  classical
  have hrow (S : β) (hS : S ∈ F) :
      (m : ℤ) - 1 + k S S ≤ ∑ T ∈ F, k S T := by
    have hlow : ((F.erase S).card : ℤ) ≤ ∑ T ∈ F.erase S, k S T := by
      calc
        _ = ∑ _T ∈ F.erase S, (1 : ℤ) := by simp
        _ ≤ _ := Finset.sum_le_sum (fun T hT =>
          hk S hS T (Finset.mem_of_mem_erase hT) (Finset.ne_of_mem_erase hT).symm)
    have he := Finset.sum_erase_add F (fun T => k S T) hS
    have hcard := Finset.card_erase_add_one hS
    rw [hc] at hcard
    have hcZ : ((F.erase S).card : ℤ) + 1 = m := by exact_mod_cast hcard
    rw [← he]
    linarith
  have hh := Finset.sum_le_sum hrow
  simp only [Finset.sum_add_distrib, Finset.sum_const, hc, nsmul_eq_mul] at hh
  nlinarith

theorem double_sum_corrected_lower {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (x y z : α)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hu : ∀ S ∈ F, S.card=4) (hc : F.card=28)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) :
    868 + ((F.filter (fun S => ({x,y,z} : Finset α) ⊆ S)).card : ℤ) -
      ((F.filter (fun S => ({x,y} : Finset α) ⊆ S)).card : ℤ) -
      ((F.filter (fun S => ({x,z} : Finset α) ⊆ S)).card : ℤ) -
      ((F.filter (fun S => ({y,z} : Finset α) ⊆ S)).card : ℤ) ≤
      ∑ S ∈ F, ∑ T ∈ F, corrected x y z (S ∩ T) := by
  classical
  have hh := double_sum_ge_diagonal F (fun S T => corrected x y z (S ∩ T)) 28 hc
    (fun S hS T hT _ => corrected_nonempty x y z hxy hxz hyz _ (hi S hS T hT))
  have he : (∑ S ∈ F, corrected x y z (S ∩ S)) =
      112 + ((F.filter (fun S => ({x,y,z} : Finset α) ⊆ S)).card : ℤ) -
      ((F.filter (fun S => ({x,y} : Finset α) ⊆ S)).card : ℤ) -
      ((F.filter (fun S => ({x,z} : Finset α) ⊆ S)).card : ℤ) -
      ((F.filter (fun S => ({y,z} : Finset α) ⊆ S)).card : ℤ) := by
    simp only [Finset.inter_self, corrected, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, sum_indicator]
    have hfour : (∑ S ∈ F, (S.card : ℤ)) = 112 := by
      calc
        _ = ∑ _S ∈ F, (4 : ℤ) := Finset.sum_congr rfl (fun S hS => by simp [hu S hS])
        _ = _ := by simp [hc]
    rw [hfour]
  rw [he] at hh
  norm_num at hh
  linarith

theorem double_sum_inter_eq {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) :
    (∑ S ∈ F, ∑ T ∈ F, ((S ∩ T).card : ℤ)) =
      ∑ v ∈ support F, (degree F v : ℤ)^2 := by
  classical
  have hn : (∑ S ∈ F, ∑ T ∈ F, (S ∩ T).card) =
      ∑ v ∈ support F, degree F v * degree F v := by
    calc
      _ = ∑ S ∈ F, ∑ v ∈ S, degree F v := by
        apply Finset.sum_congr rfl
        intro S hS
        simpa only [Finset.inter_comm, degree] using incidence_sum_eq F S
      _ = _ := FrontierSupport.weighted_incidence_sum F (degree F)
  have hn' : (∑ S ∈ F, ∑ T ∈ F, (S ∩ T).card) =
      ∑ v ∈ support F, (degree F v)^2 := by simpa only [pow_two] using hn
  exact_mod_cast hn'

theorem triple_codegree_le_two {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (C : Finset α)
    (hu : ∀ S ∈ F, S.card=4) (hf : IsSunflowerFree F 3) (hC : C.card=3) :
    (F.filter (fun S => C ⊆ S)).card ≤ 2 := by
  have hLu : ∀ P ∈ residualLink F C, P.card=1 := by
    simpa [hC] using residualLink_uniform (core := C) hu
  have hb := refined_sunflower_bound (residualLink F C) 1 3 (by decide)
    hLu (Erdos20StrictCore.residualLink_sunflowerFree hf)
  norm_num [refinedBound] at hb
  simpa [card_residualLink, upperStar] using hb

theorem three_star_sum_bound {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (x y z : α) (hc : F.card=28) :
    (degree F x : ℤ) + degree F y + degree F z ≤ 28 +
      ((F.filter (fun S => ({x,y} : Finset α) ⊆ S)).card : ℤ) +
      ((F.filter (fun S => ({x,z} : Finset α) ⊆ S)).card : ℤ) +
      ((F.filter (fun S => ({y,z} : Finset α) ⊆ S)).card : ℤ) := by
  classical
  have hrow (S : Finset α) : indicator {x} S + indicator {y} S + indicator {z} S ≤
      1 + indicator {x,y} S + indicator {x,z} S + indicator {y,z} S := by
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> by_cases hz : z ∈ S <;>
      simp [indicator, Finset.insert_subset_iff, hx,hy,hz]
  have hh := Finset.sum_le_sum (fun S (_ : S ∈ F) => hrow S)
  simpa [Finset.sum_add_distrib, sum_indicator, degree, hc] using hh

theorem two_star_sum_bound {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (x y : α) (hc : F.card=28) :
    (degree F x : ℤ) + degree F y ≤ 28 +
      ((F.filter (fun S => ({x,y} : Finset α) ⊆ S)).card : ℤ) := by
  classical
  have hrow (S : Finset α) : indicator {x} S + indicator {y} S ≤
      1 + indicator {x,y} S := by
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;>
      simp [indicator, Finset.insert_subset_iff, hx,hy]
  have hh := Finset.sum_le_sum (fun S (_ : S ∈ F) => hrow S)
  simpa [Finset.sum_add_distrib, sum_indicator, degree, hc] using hh

/-- Three distinguished stars give an exact correction to the ordinary
intersecting-family second-moment bound. No sunflower hypothesis is needed. -/
theorem three_star_second_moment {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (r : ℕ) (x y z : α)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hu : ∀ S ∈ F, S.card=r)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) :
    let M : ℤ := F.card
    let X : ℤ := ((F.filter (fun S => ({x,y} : Finset α) ⊆ S)).card : ℤ)
    let Y : ℤ := ((F.filter (fun S => ({x,z} : Finset α) ⊆ S)).card : ℤ)
    let Z : ℤ := ((F.filter (fun S => ({y,z} : Finset α) ⊆ S)).card : ℤ)
    let T : ℤ := ((F.filter (fun S => ({x,y,z} : Finset α) ⊆ S)).card : ℤ)
    M*(M+r-1) + X*(X-1) + Y*(Y-1) + Z*(Z-1) - T*(T-1) ≤
      ∑ v ∈ support F, (degree F v : ℤ)^2 := by
  classical
  have hh := double_sum_ge_diagonal F (fun S T => corrected x y z (S ∩ T))
    F.card rfl (fun S hS T hT _ =>
      corrected_nonempty x y z hxy hxz hyz _ (hi S hS T hT))
  have hdiag : (∑ S ∈ F, corrected x y z (S ∩ S)) =
      (F.card : ℤ)*r + ((F.filter (fun S => ({x,y,z} : Finset α) ⊆ S)).card : ℤ) -
      ((F.filter (fun S => ({x,y} : Finset α) ⊆ S)).card : ℤ) -
      ((F.filter (fun S => ({x,z} : Finset α) ⊆ S)).card : ℤ) -
      ((F.filter (fun S => ({y,z} : Finset α) ⊆ S)).card : ℤ) := by
    simp only [Finset.inter_self, corrected, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, sum_indicator]
    have hsum : (∑ S ∈ F, (S.card : ℤ)) = (F.card : ℤ)*r := by
      calc
        _ = ∑ _S ∈ F, (r : ℤ) :=
          Finset.sum_congr rfl (fun S hS => by rw [hu S hS])
        _ = _ := by simp
    rw [hsum]
  rw [hdiag] at hh
  simp only [corrected, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hh
  simp_rw [double_sum_indicator] at hh
  rw [double_sum_inter_eq] at hh
  dsimp only
  nlinarith only [hh]

end FrontierSupport56

#print axioms FrontierSupport56.corrected_nonempty
#print axioms FrontierSupport56.double_sum_ge_diagonal
#print axioms FrontierSupport56.double_sum_corrected_lower
#print axioms FrontierSupport56.three_star_second_moment
