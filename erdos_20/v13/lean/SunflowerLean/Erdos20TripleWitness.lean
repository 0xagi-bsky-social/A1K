import SunflowerLean.Erdos20LocalStructure

/-! Exact rank-three lower witnesses. The literal finite data are checked by
Lean's kernel reduction; no external enumeration or native evaluation is trusted. -/
namespace Erdos20TripleWitness

open Erdos20LocalStructure

/-- The ten faces of a six-point triangulation of the projective plane,
written here simply as a finite set system. -/
def tenTriples : Finset (Finset (Fin 6)) :=
  {{0,1,2}, {0,1,3}, {0,2,4}, {0,3,5}, {0,4,5},
   {1,2,5}, {1,3,4}, {1,4,5}, {2,3,4}, {2,3,5}}

/-- Two copies on disjoint six-point supports. -/
def twentyTriples : Finset (Finset (Fin 12)) :=
  {{0,1,2}, {0,1,3}, {0,2,4}, {0,3,5}, {0,4,5},
   {1,2,5}, {1,3,4}, {1,4,5}, {2,3,4}, {2,3,5},
   {6,7,8}, {6,7,9}, {6,8,10}, {6,9,11}, {6,10,11},
   {7,8,11}, {7,9,10}, {7,10,11}, {8,9,10}, {8,9,11}}

/-- Checking all ordered triples of distinct members suffices; enumerating
all subfamilies is unnecessary. -/
theorem sunflowerFree_of_no_triple {α : Type*} [DecidableEq α]
    (F : Finset (Finset α))
    (hcheck : ∀ S ∈ F, ∀ T ∈ F, ∀ U ∈ F,
      S ≠ T → S ≠ U → T ≠ U →
        ¬ (S ∩ T = S ∩ U ∧ S ∩ T = T ∩ U)) :
    IsSunflowerFree F 3 := by
  intro G hsub hsun
  obtain ⟨S, T, U, hST, hSU, hTU, hG⟩ :=
    Finset.card_eq_three.mp hsun.1
  have hS : S ∈ G := by simp [hG]
  have hT : T ∈ G := by simp [hG]
  have hU : U ∈ G := by simp [hG]
  obtain ⟨core, hcore⟩ := hsun.2
  apply hcheck S (hsub hS) T (hsub hT) U (hsub hU) hST hSU hTU
  exact ⟨(hcore S T hS hT hST).trans (hcore S U hS hU hSU).symm,
    (hcore S T hS hT hST).trans (hcore T U hT hU hTU).symm⟩

theorem tenTriples_card : tenTriples.card = 10 := by decide

theorem tenTriples_uniform : ∀ S ∈ tenTriples, S.card = 3 := by
  intro S hS
  simp only [tenTriples, Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem tenTriples_intersecting :
    ∀ S ∈ tenTriples, ∀ T ∈ tenTriples, (S ∩ T).Nonempty := by
  intro S hS T hT
  simp only [tenTriples, Finset.mem_insert, Finset.mem_singleton] at hS hT
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem tenTriples_sunflower_free : IsSunflowerFree tenTriples 3 := by
  apply sunflowerFree_of_no_triple
  intro S hS
  simp only [tenTriples, Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro T hT
    simp only [tenTriples, Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro U hU
    simp only [tenTriples, Finset.mem_insert, Finset.mem_singleton] at hU
    rcases hU with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem twentyTriples_card : twentyTriples.card = 20 := by decide

theorem twentyTriples_uniform : ∀ S ∈ twentyTriples, S.card = 3 := by
  intro S hS
  simp only [twentyTriples, Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem twentyTriples_sunflower_free : IsSunflowerFree twentyTriples 3 := by
  apply sunflowerFree_of_no_triple
  intro S hS
  simp only [twentyTriples, Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro T hT
    simp only [twentyTriples, Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro U hU
    simp only [twentyTriples, Finset.mem_insert, Finset.mem_singleton] at hU
    rcases hU with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem twenty_triples_witness : UniformFreeWitness.{0} 3 3 20 :=
  ⟨Fin 12, inferInstance, twentyTriples, twentyTriples_uniform,
    twentyTriples_sunflower_free, twentyTriples_card⟩

/-- Tensor powers give a checked lower bound in every rank divisible by three. -/
theorem twenty_power_witness (n : ℕ) :
    UniformFreeWitness.{0} 3 (3 * n) (20 ^ n) :=
  tensor_power_witness (by decide) twenty_triples_witness n

end Erdos20TripleWitness
