import SunflowerLean.Erdos20V9BoundaryArithmetic

namespace Erdos20V9Census
open Erdos20BCWConditional Erdos20Incidence Erdos20ExtremalSupport
open Erdos20DegreeCongruences Erdos20V8Boundary

/-- Supported points of a specified degree. -/
def degreeClass {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (k : ℕ) : Finset α :=
  (support F).filter (fun x => degree F x = k)

/-- Local caps on a degree predicate bound its total incidences. -/
theorem degree_predicate_incidence_le
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (p : ℕ → Prop) [DecidablePred p] (k : ℕ)
    (hcap : ∀ R ∈ F, (R.filter (fun x => p (degree F x))).card ≤ k) :
    (∑ x ∈ (support F).filter (fun x => p (degree F x)), degree F x) ≤ k * F.card := by
  classical
  let A := (support F).filter (fun x => p (degree F x))
  have he (R) (hR : R ∈ F) : R ∩ A = R.filter (fun x => p (degree F x)) := by
    ext x
    simp only [Finset.mem_inter,Finset.mem_filter,A]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,member_subset_support hR h.1,h.2⟩⟩
  change (∑ x ∈ A, degree F x) ≤ k * F.card
  change (∑ x ∈ A, (F.filter (fun R => x ∈ R)).card) ≤ k * F.card
  rw [← incidence_sum_eq]
  calc
    _ ≤ ∑ _R ∈ F, k := Finset.sum_le_sum (fun R hR => by rw [he R hR]; exact hcap R hR)
    _ = _ := by simp [Nat.mul_comm]

/-- The sum of degrees over one degree class is its degree times its size. -/
theorem degreeClass_sum
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (k : ℕ) :
    (∑ x ∈ degreeClass F k, degree F x) = k * (degreeClass F k).card := by
  calc
    _ = ∑ _x ∈ degreeClass F k, k := Finset.sum_congr rfl (fun x hx => (Finset.mem_filter.mp hx).2)
    _ = _ := by simp [Nat.mul_comm]

/-- Actual degree classes satisfy the near-boundary census and local incidence caps. -/
theorem rank_four_degree_census
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4)
    (hp : ∀ x ∈ support F, degree F x = 17 ∨ degree F x = 18 ∨ degree F x = 19 ∨ degree F x = 20)
    (h17 : ∀ R ∈ F, (R.filter (fun x => degree F x = 17)).card ≤ 1)
    (hsmall : ∀ R ∈ F, (R.filter (fun x => degree F x ≤ 18)).card ≤ 2) :
    17 * (degreeClass F 17).card + 18 * (degreeClass F 18).card +
      19 * (degreeClass F 19).card + 20 * (highPoints F).card = 4 * F.card ∧
    17 * (degreeClass F 17).card ≤ F.card ∧
    17 * (degreeClass F 17).card + 18 * (degreeClass F 18).card ≤ 2 * F.card ∧
    (support F \ highPoints F).card = (degreeClass F 17).card +
      (degreeClass F 18).card + (degreeClass F 19).card := by
  classical
  let A := degreeClass F 17
  let B := degreeClass F 18
  let C := degreeClass F 19
  let D := highPoints F
  have hdis (j k : ℕ) (hjk : j ≠ k) : Disjoint (degreeClass F j) (degreeClass F k) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact hjk ((Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hy).2)
  have hAB : Disjoint A B := hdis 17 18 (by decide)
  have hAC : Disjoint A C := hdis 17 19 (by decide)
  have hBC : Disjoint B C := hdis 18 19 (by decide)
  have hAD : Disjoint A D := hdis 17 20 (by decide)
  have hBD : Disjoint B D := hdis 18 20 (by decide)
  have hCD : Disjoint C D := hdis 19 20 (by decide)
  have hABC : Disjoint (A ∪ B) C := Finset.disjoint_union_left.mpr ⟨hAC,hBC⟩
  have hABCD : Disjoint ((A ∪ B) ∪ C) D :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hAD,hBD⟩,hCD⟩
  have hsplit : ((A ∪ B) ∪ C) ∪ D = support F := by
    ext x
    simp only [A,B,C,D,degreeClass,highPoints,Finset.mem_union,Finset.mem_filter]
    constructor
    · tauto
    · intro hx
      have hh := hp x hx
      tauto
  have hlow : support F \ highPoints F = (A ∪ B) ∪ C := by
    ext x
    simp only [A,B,C,degreeClass,highPoints,Finset.mem_sdiff,Finset.mem_union,Finset.mem_filter]
    constructor
    · rintro ⟨hx,hnot⟩
      have hh := hp x hx
      have hn : degree F x ≠ 20 := fun hh => hnot ⟨hx,hh⟩
      tauto
    · intro hx
      constructor
      · tauto
      · rintro ⟨_,hh⟩
        rcases hx with (⟨_,h⟩ | ⟨_,h⟩) | ⟨_,h⟩ <;> omega
  have hsmallset : (support F).filter (fun x => degree F x ≤ 18) = A ∪ B := by
    ext x
    simp only [A,B,degreeClass,Finset.mem_filter,Finset.mem_union]
    constructor
    · rintro ⟨hx,hle⟩
      have hh := hp x hx
      rcases hh with hh | hh | hh | hh
      · exact Or.inl ⟨hx,hh⟩
      · exact Or.inr ⟨hx,hh⟩
      · omega
      · omega
    · rintro (⟨hx,hh⟩ | ⟨hx,hh⟩) <;> exact ⟨hx,by omega⟩
  have hsumA := degreeClass_sum F 17
  have hsumB := degreeClass_sum F 18
  have hsumC := degreeClass_sum F 19
  have hsumD := degreeClass_sum F 20
  change (∑ x ∈ A, degree F x) = 17*A.card at hsumA
  change (∑ x ∈ B, degree F x) = 18*B.card at hsumB
  change (∑ x ∈ C, degree F x) = 19*C.card at hsumC
  change (∑ x ∈ D, degree F x) = 20*D.card at hsumD
  have htotal : 17*A.card + 18*B.card + 19*C.card + 20*D.card = 4*F.card := by
    rw [← hsumA,← hsumB,← hsumC,← hsumD,← Finset.sum_union hAB,
      ← Finset.sum_union hABC,← Finset.sum_union hABCD,hsplit]
    simpa [Nat.mul_comm] using support_degree_sum F 4 hu
  have ha := degree_predicate_incidence_le F (fun d => d = 17) 1 h17
  change (∑ x ∈ A, degree F x) ≤ 1 * F.card at ha
  rw [hsumA,one_mul] at ha
  have hab := degree_predicate_incidence_le F (fun d => d ≤ 18) 2 hsmall
  rw [hsmallset,Finset.sum_union hAB,hsumA,hsumB] at hab
  refine ⟨htotal,ha,hab,?_⟩
  rw [hlow,Finset.card_union_of_disjoint hABC,Finset.card_union_of_disjoint hAB]

end Erdos20V9Census
