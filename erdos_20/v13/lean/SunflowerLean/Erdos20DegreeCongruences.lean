import SunflowerLean.Erdos20ExtremalSupport

/-! Incidence congruences excluding three putative forty-two-member degree patterns. -/
namespace Erdos20DegreeCongruences
open Erdos20BCWConditional Erdos20Incidence Erdos20ExtremalSupport

/-- The number of members containing a point. -/
def degree {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x : α) : ℕ :=
  (F.filter (fun S => x ∈ S)).card

/-- Every member uses both degree classes, with one or two low-degree points. -/
def MemberPattern {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (R : Finset α) (l h : ℕ) : Prop :=
  (∀ x ∈ R, degree F x = l ∨ degree F x = h) ∧
    1 ≤ (R.filter (fun x => degree F x = l)).card ∧
    (R.filter (fun x => degree F x = l)).card ≤ 2

/-- For a four-set, the degree-sum window forces one or two points in the lower class. -/
theorem member_pattern_of_degree_sum {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (R : Finset α) (l h : ℕ)
    (hcard : R.card = 4) (hlh : l < h)
    (hp : ∀ x ∈ R, degree F x = l ∨ degree F x = h)
    (hlo : 2 * l + 2 * h ≤ ∑ x ∈ R, degree F x)
    (hhi : (∑ x ∈ R, degree F x) ≤ l + 3 * h) : MemberPattern F R l h := by
  classical
  let A := R.filter (fun x => degree F x = l)
  have hAR : A ⊆ R := Finset.filter_subset _ _
  have hsumA : (∑ x ∈ A, degree F x) = l * A.card := by
    calc
      _ = ∑ _x ∈ A, l := Finset.sum_congr rfl (fun _ hx => (Finset.mem_filter.mp hx).2)
      _ = _ := by simp [Nat.mul_comm]
  have hsumB : (∑ x ∈ R \ A, degree F x) = h * (R \ A).card := by
    calc
      _ = ∑ _x ∈ R \ A, h := by
        apply Finset.sum_congr rfl
        intro x hx
        obtain ⟨hxR,hxA⟩ := Finset.mem_sdiff.mp hx
        rcases hp x hxR with he | he
        · exact False.elim (hxA (Finset.mem_filter.mpr ⟨hxR,he⟩))
        · exact he
      _ = _ := by simp [Nat.mul_comm]
  have hsum := Finset.sum_sdiff hAR (f := fun x => degree F x)
  rw [hsumA,hsumB] at hsum
  have hcounts := Finset.card_sdiff_add_card_eq_card hAR
  rw [hcard] at hcounts
  refine ⟨hp,?_,?_⟩
  · change 1 ≤ A.card
    by_contra hn
    have ha : A.card = 0 := by omega
    have hb : (R \ A).card = 4 := by omega
    rw [ha,hb] at hsum
    nlinarith
  · change A.card ≤ 2
    by_contra hn
    have hb : (R \ A).card ≤ 1 := by omega
    have hm := Nat.mul_le_mul_left (h - l) hb
    have hd : l + (h - l) = h := Nat.add_sub_of_le (Nat.le_of_lt hlh)
    nlinarith

/-- A common degree pattern forces two incidence equations and a low-class window. -/
theorem pattern_incidence_constraints {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (r l h : ℕ)
    (hu : ∀ R ∈ F, R.card = r) (hne : l ≠ h)
    (hp : ∀ R ∈ F, MemberPattern F R l h) :
    ∃ a b : ℕ, F.card ≤ l * a ∧ l * a ≤ 2 * F.card ∧
      F.card * r = l * a + h * b := by
  classical
  let A := (support F).filter (fun x => degree F x = l)
  let B := (support F).filter (fun x => degree F x = h)
  have hsplit : A ∪ B = support F := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_filter.mp hx).1
      · exact (Finset.mem_filter.mp hx).1
    · intro hx
      obtain ⟨R,hR,hxR⟩ := Finset.mem_biUnion.mp hx
      rcases (hp R hR).1 x hxR with hl | hh
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx,hl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx,hh⟩)
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxB
    exact hne ((Finset.mem_filter.mp hxA).2.symm.trans (Finset.mem_filter.mp hxB).2)
  have hsumA : (∑ x ∈ A, degree F x) = l * A.card := by
    calc
      _ = ∑ _x ∈ A, l := Finset.sum_congr rfl (fun _ hx => (Finset.mem_filter.mp hx).2)
      _ = _ := by simp [Nat.mul_comm]
  have hsumB : (∑ x ∈ B, degree F x) = h * B.card := by
    calc
      _ = ∑ _x ∈ B, h := Finset.sum_congr rfl (fun _ hx => (Finset.mem_filter.mp hx).2)
      _ = _ := by simp [Nat.mul_comm]
  have htotal : F.card * r = l * A.card + h * B.card := by
    rw [← hsumA,← hsumB,← Finset.sum_union hdis,hsplit]
    exact (support_degree_sum F r hu).symm
  have hshape (R : Finset α) (hR : R ∈ F) :
      R ∩ A = R.filter (fun x => degree F x = l) := by
    ext x
    simp only [Finset.mem_inter,Finset.mem_filter,A]
    exact ⟨fun hx => ⟨hx.1,hx.2.2⟩,
      fun hx => ⟨hx.1,member_subset_support hR hx.1,hx.2⟩⟩
  have hlo : F.card ≤ ∑ R ∈ F, (R ∩ A).card := by
    calc
      _ = ∑ _R ∈ F, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun R hR => by rw [hshape R hR]; exact (hp R hR).2.1)
  have hhi : (∑ R ∈ F, (R ∩ A).card) ≤ 2 * F.card := by
    calc
      _ ≤ ∑ _R ∈ F, 2 := Finset.sum_le_sum (fun R hR => by rw [hshape R hR]; exact (hp R hR).2.2)
      _ = _ := by simp [Nat.mul_comm]
  rw [incidence_sum_eq] at hlo hhi
  change F.card ≤ ∑ x ∈ A, degree F x at hlo
  change (∑ x ∈ A, degree F x) ≤ 2 * F.card at hhi
  rw [hsumA] at hlo hhi
  exact ⟨A.card,B.card,hlo,hhi,htotal⟩

/-- Intersecting members cannot belong to disjoint pairs of global degree classes. -/
theorem member_patterns_incompatible {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (R S : Finset α) (l h l' h' : ℕ)
    (hR : MemberPattern F R l h) (hS : MemberPattern F S l' h')
    (hi : (R ∩ S).Nonempty)
    (hex : ∀ d : ℕ, (d = l ∨ d = h) → (d = l' ∨ d = h') → False) : False := by
  obtain ⟨x,hx⟩ := hi
  obtain ⟨hxR,hxS⟩ := Finset.mem_inter.mp hx
  exact hex (degree F x) (hR.1 x hxR) (hS.1 x hxS)

/-- Three locally admissible degree patterns cannot describe an intersecting family
of forty-two four-sets. No sunflower-freeness hypothesis is required. -/
theorem no_forty_two_degree_patterns {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card = 4)
    (hi : ∀ R ∈ F, ∀ S ∈ F, (R ∩ S).Nonempty) (hc : F.card = 42)
    (hp : ∀ R ∈ F, MemberPattern F R 12 13 ∨
      MemberPattern F R 14 17 ∨ MemberPattern F R 15 16) : False := by
  obtain ⟨R,hR⟩ := Finset.card_pos.mp (show 0 < F.card by omega)
  rcases hp R hR with h12 | h14 | h15
  · have hall : ∀ S ∈ F, MemberPattern F S 12 13 := by
      intro S hS
      rcases hp S hS with h | h | h
      · exact h
      · exact False.elim (member_patterns_incompatible F R S 12 13 14 17
          h12 h (hi R hR S hS) (by intro d ha hb; omega))
      · exact False.elim (member_patterns_incompatible F R S 12 13 15 16
          h12 h (hi R hR S hS) (by intro d ha hb; omega))
    obtain ⟨a,b,hlo,hhi,he⟩ := pattern_incidence_constraints F 4 12 13 hu (by omega) hall
    rw [hc] at hlo hhi he
    omega
  · have hall : ∀ S ∈ F, MemberPattern F S 14 17 := by
      intro S hS
      rcases hp S hS with h | h | h
      · exact False.elim (member_patterns_incompatible F R S 14 17 12 13
          h14 h (hi R hR S hS) (by intro d ha hb; omega))
      · exact h
      · exact False.elim (member_patterns_incompatible F R S 14 17 15 16
          h14 h (hi R hR S hS) (by intro d ha hb; omega))
    obtain ⟨a,b,hlo,hhi,he⟩ := pattern_incidence_constraints F 4 14 17 hu (by omega) hall
    rw [hc] at hlo hhi he
    omega
  · have hall : ∀ S ∈ F, MemberPattern F S 15 16 := by
      intro S hS
      rcases hp S hS with h | h | h
      · exact False.elim (member_patterns_incompatible F R S 15 16 12 13
          h15 h (hi R hR S hS) (by intro d ha hb; omega))
      · exact False.elim (member_patterns_incompatible F R S 15 16 14 17
          h15 h (hi R hR S hS) (by intro d ha hb; omega))
      · exact h
    obtain ⟨a,b,hlo,hhi,he⟩ := pattern_incidence_constraints F 4 15 16 hu (by omega) hall
    rw [hc] at hlo hhi he
    omega

end Erdos20DegreeCongruences
