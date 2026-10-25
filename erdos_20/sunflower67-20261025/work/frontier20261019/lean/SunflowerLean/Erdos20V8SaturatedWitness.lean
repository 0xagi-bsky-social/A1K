import SunflowerLean.Erdos20TripleWitness
import SunflowerLean.Erdos20RankFour

/-! A finite exact witness attaining the saturated-singleton rank-four bound. -/
namespace Erdos20V8SaturatedWitness
open Erdos20RankThree

/-- The ten-design in two center layers and the six-edge center-pair layer. -/
def mask : Fin 26 → ℕ :=
  ![4103, 4107, 4117, 4137, 4145, 4134, 4122, 4146, 4124, 4140, 8199, 8203, 8213, 8233, 8241, 8230, 8218, 8242, 8220, 8236, 12480, 12608, 12672, 13824, 14848, 15360]

/-- Decode the fourteen ground-set membership bits. -/
def member (i : Fin 26) : Finset (Fin 14) :=
  Finset.univ.filter (fun x => (mask i).testBit x.val = true)

/-- The twenty-six displayed members. -/
def family : Finset (Finset (Fin 14)) := Finset.univ.image member

/-- An exact arithmetic encoding of an actual finite set. -/
def setCode (S : Finset (Fin 14)) : ℕ := ∑ x ∈ S, 2 ^ x.val

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Every pairwise intersection is checked against its integer bitmask code. -/
theorem pair_code_check : ∀ i j : Fin 26,
    setCode (member i ∩ member j) = (mask i &&& mask j) := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Exhaustive distinct-index comparison, reduced through the kernel's ordinary decidability path. -/
theorem no_three_equal_intersection_codes : ∀ i j k : Fin 26,
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
theorem members_uniform_check : ∀ i : Fin 26, (member i).card = 4 := by decide

/-- Literal four-uniformity, with no numerical proxy left in the conclusion. -/
theorem family_uniform : ∀ S ∈ family, S.card = 4 := by
  intro S hS
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hS
  exact members_uniform_check i

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- All pairwise intersection codes are positive. -/
theorem positive_intersection_codes : ∀ i j : Fin 26, 0 < (mask i &&& mask j) := by decide

/-- Literal pairwise intersection follows from the exact checked set-code bridge. -/
theorem family_intersecting : ∀ S ∈ family, ∀ T ∈ family, (S ∩ T).Nonempty := by
  intro S hS T hT
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hS
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hT
  by_contra hn
  have he : member i ∩ member j = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hpos := positive_intersection_codes i j
  rw [← pair_code_check,he] at hpos
  simp [setCode] at hpos

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The image contains twenty-six distinct four-sets. -/
theorem family_card : family.card = 26 := by decide

/-- A member from the center-pair layer. -/
def anchor : Finset (Fin 14) := {12,13,6,7}

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The selected four-set is an actual family member. -/
theorem anchor_mem : anchor ∈ family := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The exact singleton trace at the first center has ten members. -/
theorem singleton_trace_ten : (exactTrace family anchor {12}).card = 10 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Both center point degrees attain sixteen. -/
theorem center_degrees_sixteen :
    (family.filter (fun S => (12 : Fin 14) ∈ S)).card = 16 ∧
    (family.filter (fun S => (13 : Fin 14) ∈ S)).card = 16 := by decide

/-- An explicit twenty-six-member witness with an actual saturated singleton trace. -/
theorem saturated_twenty_six_witness :
    ∃ F : Finset (Finset (Fin 14)), F.card = 26 ∧
      (∀ S ∈ F, S.card = 4) ∧ IsSunflowerFree F 3 ∧
      (∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) ∧
      ∃ R ∈ F, ∃ x ∈ R, (exactTrace F R {x}).card = 10 := by
  exact ⟨family,family_card,family_uniform,family_sunflower_free,family_intersecting,
    anchor,anchor_mem,12,by decide,singleton_trace_ten⟩

end Erdos20V8SaturatedWitness
