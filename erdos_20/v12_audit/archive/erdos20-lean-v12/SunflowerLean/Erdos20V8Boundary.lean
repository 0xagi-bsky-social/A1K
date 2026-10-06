import SunflowerLean.Erdos20DegreeCongruences

namespace Erdos20V8Boundary
open Erdos20BCWConditional Erdos20Incidence Erdos20ExtremalSupport Erdos20DegreeCongruences

/-- The supported degree-twenty points of a family. -/
def highPoints {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Finset α :=
  (support F).filter (fun x => degree F x = 20)

/-- With83 four-sets and only degrees19and20, the support and degree classes
are forced. This is a finite incidence identity, with no sunflower assumption. -/
theorem degree_classes_of_eighty_three
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hc : F.card = 83)
    (hp : ∀ x ∈ support F, degree F x = 19 ∨ degree F x = 20) :
    (support F).card = 17 ∧ (highPoints F).card = 9 ∧
      ((support F).filter (fun x => degree F x = 19)).card = 8 := by
  classical
  let A := (support F).filter (fun x => degree F x = 19)
  let B := highPoints F
  have hsplit : A ∪ B = support F := by
    ext x
    simp only [Finset.mem_union,Finset.mem_filter,A,B,highPoints]
    exact ⟨fun h => h.elim And.left And.left, fun hx => (hp x hx).elim
      (fun h => Or.inl ⟨hx,h⟩) (fun h => Or.inr ⟨hx,h⟩)⟩
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have h19 := (Finset.mem_filter.mp hx).2
    have h20 := (Finset.mem_filter.mp hy).2
    omega
  have hsumA : (∑ x ∈ A, degree F x) = 19 * A.card := by
    calc
      _ = ∑ _x ∈ A, 19 := Finset.sum_congr rfl (fun _ hx => (Finset.mem_filter.mp hx).2)
      _ = _ := by simp [Nat.mul_comm]
  have hsumB : (∑ x ∈ B, degree F x) = 20 * B.card := by
    calc
      _ = ∑ _x ∈ B, 20 := Finset.sum_congr rfl (fun _ hx => (Finset.mem_filter.mp hx).2)
      _ = _ := by simp [Nat.mul_comm]
  have htotal : 332 = 19 * A.card + 20 * B.card := by
    rw [← hsumA,← hsumB,← Finset.sum_union hdis,hsplit]
    change 332 = ∑ x ∈ support F, (F.filter (fun R => x ∈ R)).card
    rw [support_degree_sum F 4 hu,hc]
  have hn : (support F).card = A.card + B.card := by
    rw [← hsplit,Finset.card_union_of_disjoint hdis]
  change (support F).card = 17 ∧ B.card = 9 ∧ A.card = 8
  clear * - htotal hn
  omega

/-- Integer-scaled reciprocal high-point multiplicity around a point. -/
def pointWeight {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (H : Finset α) (x : α) : ℕ :=
  ∑ R ∈ F.filter (fun R => x ∈ R), 6 / (R ∩ H).card

/-- High-point reciprocal weights count each member exactly six times. -/
theorem weighted_high_point_incidence
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (H : Finset α)
    (hm : ∀ R ∈ F, 1 ≤ (R ∩ H).card ∧ (R ∩ H).card ≤ 3) :
    (∑ x ∈ H, pointWeight F H x) = 6 * F.card := by
  classical
  unfold pointWeight
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  have hsingle (R : Finset α) (hR : R ∈ F) :
      (∑ x ∈ H, if x ∈ R then 6 / (R ∩ H).card else 0) = 6 := by
    have he : H.filter (fun x => x ∈ R) = R ∩ H := by
      ext x
      simp [and_comm]
    rw [← Finset.sum_filter,he]
    simp only [Finset.sum_const,Nat.nsmul_eq_mul]
    obtain ⟨hlo,hhi⟩ := hm R hR
    have hc : (R ∩ H).card = 1 ∨ (R ∩ H).card = 2 ∨ (R ∩ H).card = 3 := by omega
    rcases hc with hc | hc | hc <;> rw [hc]
  calc
    _ = ∑ _R ∈ F, 6 := Finset.sum_congr rfl hsingle
    _ = _ := by simp [Nat.mul_comm]

end Erdos20V8Boundary
