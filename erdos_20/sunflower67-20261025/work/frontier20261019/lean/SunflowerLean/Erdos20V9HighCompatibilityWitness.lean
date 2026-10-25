import SunflowerLean.Erdos20TripleWitness
import SunflowerLean.Erdos20V9HighCompatibilityMain

/-! A finite exact witness showing the unconditional two-high cap is sharp. -/
namespace Erdos20V9HighCompatibilityWitness
open Erdos20RankThree Erdos20V8Boundary Erdos20DegreeCongruences

/-- Two compatible degree-twenty stars sharing five members. -/
def mask : Fin 35 → ℕ :=
  ![15, 27, 45, 51, 53, 71, 78, 85, 89, 90, 99, 105, 108, 114, 116, 897, 960, 1793, 1856, 2689, 2752, 3201, 3264, 3329, 3392, 4481, 4544, 5249, 5312, 5633, 5696, 6401, 6464, 6657, 6720]

/-- Decode the thirteen ground-set membership bits. -/
def member (i : Fin 35) : Finset (Fin 13) :=
  Finset.univ.filter (fun x => (mask i).testBit x.val = true)

/-- The thirty-five displayed members. -/
def family : Finset (Finset (Fin 13)) := Finset.univ.image member

/-- An exact arithmetic encoding of an actual finite set. -/
def setCode (S : Finset (Fin 13)) : ℕ := ∑ x ∈ S, 2 ^ x.val

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Every pairwise intersection is checked against its integer bitmask code. -/
theorem pair_code_check : ∀ i j : Fin 35,
    setCode (member i ∩ member j) = (mask i &&& mask j) := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Exhaustive distinct-index comparison, reduced through the kernel's ordinary decidability path. -/
theorem no_three_equal_intersection_codes : ∀ i j k : Fin 35,
    i ≠ j → i ≠ k → j ≠ k →
    ¬ ((mask i &&& mask j) = (mask i &&& mask k) ∧
       (mask i &&& mask j) = (mask j &&& mask k)) := by decide

/-- Transfer the finite arithmetic certificate to the literal sunflower-free proposition. -/
theorem family_sunflower_free : IsSunflowerFree family 3 := by
  apply Erdos20TripleWitness.sunflowerFree_of_no_triple
  intro S hS T hT U hU hST hSU hTU
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hS
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hT
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hU
  intro hh
  have hij : i ≠ j := fun he => hST (congrArg member he)
  have hik : i ≠ k := fun he => hSU (congrArg member he)
  have hjk : j ≠ k := fun he => hTU (congrArg member he)
  apply no_three_equal_intersection_codes i j k hij hik hjk
  have ha := congrArg setCode hh.1
  have hb := congrArg setCode hh.2
  rw [pair_code_check,pair_code_check] at ha hb
  exact ⟨ha,hb⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Every displayed member has exactly four points. -/
theorem members_uniform_check : ∀ i : Fin 35, (member i).card = 4 := by decide

/-- Literal four-uniformity, with no numerical proxy left in the conclusion. -/
theorem family_uniform : ∀ S ∈ family, S.card = 4 := by
  intro S hS
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hS
  exact members_uniform_check i

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The image contains thirty-five distinct four-sets. -/
theorem family_card : family.card = 35 := by decide

/-- A member containing both high points. -/
def anchor : Finset (Fin 13) := {0,6,1,2}

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The selected anchor belongs to the actual family. -/
theorem anchor_mem : anchor ∈ family := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Exactly the two displayed centers have degree twenty. -/
theorem high_points_check : highPoints family = {0,6} := by decide

/-- The selected member attains the two-high cap. -/
theorem anchor_high_count_two : (anchor ∩ highPoints family).card = 2 := by
  rw [high_points_check]
  decide

/-- A literal sunflower-free witness showing that the unconditional cap two
cannot be reduced to one. -/
theorem two_high_member_witness :
    ∃ F : Finset (Finset (Fin 13)), F.card = 35 ∧
      (∀ S ∈ F, S.card = 4) ∧ IsSunflowerFree F 3 ∧
      ∃ R ∈ F, (R ∩ highPoints F).card = 2 := by
  exact ⟨family,family_card,family_uniform,family_sunflower_free,
    anchor,anchor_mem,anchor_high_count_two⟩

end Erdos20V9HighCompatibilityWitness
