import SunflowerLean.Erdos20TripleWitness
import SunflowerLean.Erdos20V9HighCompatibilityMain

/-! A finite exact witness showing the unconditional two-high cap is sharp. -/
namespace FrontierSharp45
open Erdos20RankThree Erdos20V8Boundary Erdos20DegreeCongruences

/-- Two disjoint degree-twenty stars and five further members. -/
def masks : Array Nat := #[4544, 4800, 5440, 6720, 7232, 8199, 8203, 8213, 8218, 8220, 8230, 8233, 8236, 8241, 8242, 8640, 8896, 9536, 9856, 9984, 10624, 10816, 11008, 11328, 11392, 16391, 16395, 16405, 16410, 16412, 16422, 16425, 16428, 16433, 16434, 18048, 18176, 18816, 19200, 19584, 20864, 21120, 21760, 23040, 23552]
def mask (i : Fin 45) : Nat := masks[i.val]!

/-- Decode the fifteen ground-set membership bits. -/
def member (i : Fin 45) : Finset (Fin 15) :=
  Finset.univ.filter (fun x => (mask i).testBit x.val = true)

/-- The forty-five displayed members. -/
def family : Finset (Finset (Fin 15)) := Finset.univ.image member

def decode (n : Nat) : Finset (Fin 15) :=
  Finset.univ.filter (fun x => n.testBit x.val = true)

theorem decode_and (a b : Nat) : decode (a &&& b) = decode a ∩ decode b := by
  ext v
  simp [decode, Nat.testBit_and, Bool.and_eq_true]

theorem decode_injective_bounded {a b : Nat} (ha : a < 2^15) (hb : b < 2^15)
    (h : decode a = decode b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 15
  · have he := Finset.ext_iff.mp h (⟨i,hi⟩ : Fin 15)
    simp only [decode, Finset.mem_filter, Finset.mem_univ, true_and] at he
    exact Bool.eq_iff_iff.mpr he
  · have hp : 2^15 ≤ 2^i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hp),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hp)]

theorem masks_bound : ∀ i : Fin 45, mask i < 2^15 := by decide

theorem pair_mask_eq_of_inter_eq (i j k l : Fin 45)
    (h : member i ∩ member j = member k ∩ member l) :
    (mask i &&& mask j) = (mask k &&& mask l) := by
  apply decode_injective_bounded
    (lt_of_le_of_lt Nat.and_le_left (masks_bound i))
    (lt_of_le_of_lt Nat.and_le_left (masks_bound k))
  simpa only [decode_and] using h

#check pair_mask_eq_of_inter_eq

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
/-- Exhaustive distinct-index comparison, reduced through the kernel's ordinary decidability path. -/
theorem no_three_equal_intersection_codes : ∀ i j k : Fin 45,
    i ≠ j → i ≠ k → j ≠ k →
    ¬ ((mask i &&& mask j) = (mask i &&& mask k) ∧
       (mask i &&& mask j) = (mask j &&& mask k)) := by decide

#check no_three_equal_intersection_codes

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
  exact ⟨pair_mask_eq_of_inter_eq i j i k hh.1,
    pair_mask_eq_of_inter_eq i j j k hh.2⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
/-- Every displayed member has exactly four points. -/
theorem members_uniform_check : ∀ i : Fin 45, (member i).card = 4 := by decide

/-- Literal four-uniformity, with no numerical proxy left in the conclusion. -/
theorem family_uniform : ∀ S ∈ family, S.card = 4 := by
  intro S hS
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hS
  exact members_uniform_check i

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
/-- The image contains forty-five distinct four-sets. -/
theorem family_card : family.card = 45 := by decide


set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem high_points_check : highPoints family = {13,14} := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem centers_degree : Erdos20BCWConditional.degree family 13 = 20 ∧
    Erdos20BCWConditional.degree family 14 = 20 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem no_joint_member : ∀ S ∈ family, ¬ ((13 : Fin 15) ∈ S ∧ (14 : Fin 15) ∈ S) := by decide

theorem literal_forty_five_two_independent_high_witness :
    ∃ F : Finset (Finset (Fin 15)), F.card = 45 ∧
      (∀ S ∈ F, S.card = 4) ∧ IsSunflowerFree F 3 ∧
      Erdos20BCWConditional.degree F 13 = 20 ∧
      Erdos20BCWConditional.degree F 14 = 20 ∧
      (∀ S ∈ F, ¬ ((13 : Fin 15) ∈ S ∧ (14 : Fin 15) ∈ S)) := by
  exact ⟨family, family_card, family_uniform, family_sunflower_free,
    centers_degree.1, centers_degree.2, no_joint_member⟩

end FrontierSharp45
