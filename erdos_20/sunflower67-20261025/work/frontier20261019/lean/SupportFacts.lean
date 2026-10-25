import Support56

namespace FrontierSupportFacts
open Erdos20BCWConditional Erdos20DegreeCongruences Erdos20Incidence
open FrontierSupport56
universe u

theorem degree_pos {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (x : α) (hx : x ∈ support F) : 1 ≤ degree F x := by
  obtain ⟨S,hS,hxS⟩ := Finset.mem_biUnion.mp hx
  exact Finset.card_pos.mpr ⟨S,Finset.mem_filter.mpr ⟨hS,hxS⟩⟩

theorem degree_sum {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (r : ℕ) (hu : ∀ S∈F, S.card=r) :
    (∑ x ∈ support F, degree F x) = r * F.card := by
  have h := incidence_sum_eq F (support F)
  have hh : (∑ S∈F, (S∩support F).card) = r*F.card := by
    calc
      _ = ∑ _S∈F, r := Finset.sum_congr rfl (fun S hS => by
        rw [Finset.inter_eq_left.mpr (member_subset_support hS),hu S hS])
      _ = _ := by simp [Nat.mul_comm]
  simpa [degree] using h.symm.trans hh

theorem degree_sum_twenty_eight {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S∈F, S.card=4) (hc : F.card=28) :
    (∑ x∈support F, (degree F x : ℤ))=112 := by
  have h := degree_sum F 4 hu
  rw [hc] at h
  exact_mod_cast h

theorem pair_bound {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S∈F, S.card=4) (hf : IsSunflowerFree F 3)
    (x y : α) (hxy : x≠y) :
    ((F.filter (fun S => ({x,y} : Finset α) ⊆ S)).card : ℤ) ≤ 6 := by
  have h := Erdos20V11Census.rank_four_pair_codegree_le_six F hu hf x y hxy
  change (F.filter (fun S => ({x,y} : Finset α) ⊆ S)).card ≤ 6 at h
  exact_mod_cast h

theorem triple_bound {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S∈F, S.card=4) (hf : IsSunflowerFree F 3)
    (x y z : α) (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) :
    ((F.filter (fun S => ({x,y,z} : Finset α) ⊆ S)).card : ℤ) ≤ 2 := by
  have h := triple_codegree_le_two F {x,y,z} hu hf (by simp [hxy,hxz,hyz])
  exact_mod_cast h

theorem two_degree_bound {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S∈F, S.card=4) (hf : IsSunflowerFree F 3)
    (hc : F.card=28) (x y : α) (hxy : x≠y) : degree F x + degree F y ≤ 34 := by
  have h := two_star_sum_bound F x y hc
  have hp := pair_bound F hu hf x y hxy
  have hz : (degree F x : ℤ) + degree F y ≤ 34 := by linarith
  exact_mod_cast hz

theorem three_degree_bound {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S∈F, S.card=4) (hf : IsSunflowerFree F 3)
    (hc : F.card=28) (x y z : α) (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) :
    degree F x + degree F y + degree F z ≤ 46 := by
  have h := three_star_sum_bound F x y z hc
  have hxy6 := pair_bound F hu hf x y hxy
  have hxz6 := pair_bound F hu hf x z hxz
  have hyz6 := pair_bound F hu hf y z hyz
  have hz : (degree F x : ℤ)+degree F y+degree F z ≤ 46 := by linarith
  exact_mod_cast hz

theorem quadratic_sum_eq {α : Type u} [DecidableEq α]
    (s : Finset α) (w : α → ℕ) :
    (∑ x∈s, (w x : ℤ)*((w x : ℤ)-1)) =
      (∑ x∈s, (w x : ℤ)^2) - ∑ x∈s, (w x : ℤ) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

end FrontierSupportFacts
