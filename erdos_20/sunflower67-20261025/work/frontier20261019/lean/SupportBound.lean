import SunflowerLean.Erdos20V13FiniteReduction
import SunflowerLean.Erdos20ExtremalTransversals

namespace FrontierSupport
open Erdos20BCWConditional Erdos20DegreeCongruences Erdos20Incidence
open Erdos20V8Targets Erdos20V13FiniteReduction

universe u

/-- Weighted incidence counting, over the actual support of a finite family. -/
theorem weighted_incidence_sum {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (w : α → ℕ) :
    (∑ S ∈ F, ∑ x ∈ S, w x) = ∑ x ∈ support F, degree F x * w x := by
  classical
  have he (S : Finset α) (hS : S ∈ F) :
      (support F).filter (fun x => x ∈ S) = S := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hx => ⟨member_subset_support hS hx, hx⟩⟩
  calc
    _ = ∑ S ∈ F, ∑ x ∈ support F, if x ∈ S then w x else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [← Finset.sum_filter, he S hS]
    _ = ∑ x ∈ support F, ∑ S ∈ F, if x ∈ S then w x else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.sum_filter]
      simp [degree]

/-- A support bound for every intersecting uniform finite family with bounded
point degree. No sunflower hypothesis is needed for this counting inequality. -/
theorem intersecting_degree_support_inequality {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (r D : ℕ)
    (hu : ∀ S ∈ F, S.card = r)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (hd : ∀ x, degree F x ≤ D) :
    D * (support F).card + F.card * (F.card + (r - 1)) ≤
      (D + 1) * (r * F.card) := by
  classical
  have hlow (S : Finset α) (hS : S ∈ F) :
      F.card + (r - 1) ≤ ∑ x ∈ S, degree F x := by
    have h := incidence_defect_lower_bound F {S} S r (by simpa using hS)
      (by intro T hT; simpa only [Finset.mem_singleton.mp hT] using hu S hS)
      (by intro T hT; have he := Finset.mem_singleton.mp hT; subst T; exact Finset.Subset.refl _)
      (fun T hT => hi T hT S hS)
    simpa [degree] using h
  have hlowSum := Finset.sum_le_sum hlow
  have hw := weighted_incidence_sum F (degree F)
  simp only [Finset.sum_const, smul_eq_mul] at hlowSum
  rw [hw] at hlowSum
  have hpoint (x : α) (hx : x ∈ support F) :
      D + degree F x * degree F x ≤ (D + 1) * degree F x := by
    have hpos : 1 ≤ degree F x := by
      obtain ⟨S,hS,hxS⟩ := Finset.mem_biUnion.mp hx
      exact Finset.card_pos.mpr ⟨S, Finset.mem_filter.mpr ⟨hS,hxS⟩⟩
    have htop := hd x
    nlinarith
  have hupper := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib] at hupper
  simp only [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at hupper
  have htotal : (∑ x ∈ support F, degree F x) = r * F.card := by
    have h := incidence_sum_eq F (support F)
    have hh : (∑ S ∈ F, (S ∩ support F).card) = r * F.card := by
      calc
        _ = ∑ _S ∈ F, r := Finset.sum_congr rfl (fun S hS => by
          rw [Finset.inter_eq_left.mpr (member_subset_support hS), hu S hS])
        _ = _ := by simp [Nat.mul_comm]
    simpa [degree] using h.symm.trans hh
  rw [htotal] at hupper
  nlinarith

theorem intersecting_twenty_eight_support_le_seventy_two
    {α : Type u} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 28) :
    (support F).card ≤ 72 := by
  have hd : ∀ x, degree F x ≤ 19 :=
    Erdos20ExtremalTransversals.intersecting_rank_four_card_ge_twenty_one_degree_le_nineteen
      F hu hf hi (by omega)
  have h := intersecting_degree_support_inequality F 4 19 hu hi hd
  rw [hc] at h
  omega

/-- A finite obstruction predicate with an explicit ambient capacity. -/
def FiniteIntersectingObstructionOn (n : ℕ) : Prop :=
  ∃ G : Finset (Finset (Fin n)), G.card = 28 ∧
    (∀ S ∈ G, S.card = 4) ∧ IsSunflowerFree G 3 ∧
    (∀ S ∈ G, ∀ T ∈ G, (S ∩ T).Nonempty)

/-- Any intersecting counterexample yields an exact-size obstruction on 72 points. -/
theorem finite72_obstruction_of_counterexample
    {α : Type u} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : 27 < F.card) :
    FiniteIntersectingObstructionOn 72 := by
  obtain ⟨H,hsub,hcard⟩ := Finset.exists_subset_card_eq (show 28 ≤ F.card by omega)
  have hHu : ∀ S ∈ H, S.card = 4 := fun S hS => hu S (hsub hS)
  have hHf : IsSunflowerFree H 3 := fun G hG => hf G (hG.trans hsub)
  have hHi : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty :=
    fun S hS T hT => hi S (hsub hS) T (hsub hT)
  have hs := intersecting_twenty_eight_support_le_seventy_two H hHu hHf hHi hcard
  obtain ⟨G,hGc,hGu,hGf,hGi⟩ := exists_intersecting_fin_relabel H 72 4 3 hs hHu hHf hHi
  exact ⟨G,hGc.trans hcard,hGu,hGf,hGi⟩

/-- Unconditional exact equivalence; it does not assert obstruction nonexistence. -/
theorem intersecting_upper_twenty_seven_iff_no_finite72_obstruction :
    IntersectingRankFourUpper 27 ↔ ¬ FiniteIntersectingObstructionOn 72 := by
  constructor
  · intro hI hobs
    obtain ⟨G,hc,hu,hf,hi⟩ := hobs
    have hb := hI G hu hf hi
    omega
  · intro hn α inst F hu hf hi
    by_contra hnot
    exact hn (finite72_obstruction_of_counterexample F hu hf hi (by omega))

/-- Boolean-incidence semantics behind a three-sunflower constraint: pairwise
intersections agree exactly when no point belongs to exactly two sets. -/
theorem equal_intersections_iff_no_exact_two
    {α : Type u} [DecidableEq α] (A B C : Finset α) :
    (A ∩ B = A ∩ C ∧ A ∩ B = B ∩ C) ↔
    ∀ x, ¬ ((x ∈ A ∧ x ∈ B ∧ x ∉ C) ∨
      (x ∈ A ∧ x ∉ B ∧ x ∈ C) ∨ (x ∉ A ∧ x ∈ B ∧ x ∈ C)) := by
  constructor
  · rintro ⟨h1,h2⟩ x
    have e1 := Finset.ext_iff.mp h1 x
    have e2 := Finset.ext_iff.mp h2 x
    simp only [Finset.mem_inter] at e1 e2
    tauto
  · intro h
    constructor <;> ext x <;> have hx := h x <;>
      simp only [Finset.mem_inter] <;> tauto

end FrontierSupport
#print axioms FrontierSupport.weighted_incidence_sum
#print axioms FrontierSupport.intersecting_degree_support_inequality
#print axioms FrontierSupport.intersecting_twenty_eight_support_le_seventy_two

#print axioms FrontierSupport.finite72_obstruction_of_counterexample
#print axioms FrontierSupport.intersecting_upper_twenty_seven_iff_no_finite72_obstruction
#print axioms FrontierSupport.equal_intersections_iff_no_exact_two
