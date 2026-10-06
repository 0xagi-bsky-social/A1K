import SunflowerLean.Erdos20V8Boundary
import SunflowerLean.Erdos20V8DesignCounts

/-! A divisibility obstruction to a degree-eighteen point surrounded by
 degree-twenty points. All finite incidence hypotheses are explicit. -/
namespace Erdos20V8HighDegrees
open Erdos20BCWConditional Erdos20Incidence Erdos20DegreeCongruences Erdos20V8Boundary

/-- The incidence sum over the star of a point counts its codegrees into a set. -/
theorem star_pair_incidence_sum
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (H : Finset α) (x : α) :
    (∑ R ∈ F.filter (fun R => x ∈ R), (R ∩ H).card) =
      ∑ y ∈ H, (F.filter (fun R => {x,y} ⊆ R)).card := by
  classical
  rw [incidence_sum_eq]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  ext R
  simp [Finset.insert_subset_iff,and_assoc]

/-- If all codegrees into a set are divisible by five and every star member
 meets it in exactly three points, three times the point degree is divisible by five. -/
theorem five_dvd_three_times_degree
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (H : Finset α) (x : α)
    (hlocal : ∀ R ∈ F, x ∈ R → (R ∩ H).card = 3)
    (hpairs : ∀ y ∈ H, 5 ∣ (F.filter (fun R => {x,y} ⊆ R)).card) :
    5 ∣ 3 * degree F x := by
  classical
  have hsum : (∑ R ∈ F.filter (fun R => x ∈ R), (R ∩ H).card) =
      3 * degree F x := by
    calc
      _ = ∑ _R ∈ F.filter (fun R => x ∈ R), 3 := by
        apply Finset.sum_congr rfl
        intro R hR
        exact hlocal R (Finset.mem_filter.mp hR).1 (Finset.mem_filter.mp hR).2
      _ = _ := by simp [degree,Nat.mul_comm]
  rw [← hsum,star_pair_incidence_sum]
  exact Finset.dvd_sum hpairs

/-- A degree-eighteen point cannot have three high neighbors in every member
 when all its codegrees into the degree-twenty class are zero or five. -/
theorem no_degree_eighteen_of_high_neighbors_and_pair_degrees
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x : α)
    (hu : ∀ R ∈ F, R.card = 4)
    (hlocal : ∀ R ∈ F, x ∈ R → ∀ y ∈ R, y ≠ x → degree F y = 20)
    (hpairs : ∀ y ∈ highPoints F,
      (F.filter (fun R => {x,y} ⊆ R)).card = 0 ∨
      (F.filter (fun R => {x,y} ⊆ R)).card = 5) : degree F x ≠ 18 := by
  classical
  intro hx18
  have hcard : ∀ R ∈ F, x ∈ R → (R ∩ highPoints F).card = 3 := by
    intro R hR hxR
    have he : R ∩ highPoints F = R.erase x := by
      ext y
      simp only [Finset.mem_inter,highPoints,Finset.mem_filter,Finset.mem_erase]
      constructor
      · rintro ⟨hyR,hyS,hy20⟩
        refine ⟨?_,hyR⟩
        intro heq
        subst y
        omega
      · rintro ⟨hne,hyR⟩
        exact ⟨hyR,member_subset_support hR hyR,hlocal R hR hxR y hyR hne⟩
    rw [he,Finset.card_erase_of_mem hxR,hu R hR]
  have hdiv := five_dvd_three_times_degree F (highPoints F) x hcard (by
    intro y hy
    rcases hpairs y hy with he | he <;> simp [he])
  rw [hx18] at hdiv
  norm_num at hdiv

/-- In a sunflower-free four-uniform family, a point all of whose co-members
 have degree twenty cannot itself have degree eighteen. -/
theorem no_degree_eighteen_of_high_neighbors
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x : α)
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (hlocal : ∀ R ∈ F, x ∈ R → ∀ y ∈ R, y ≠ x → degree F y = 20) :
    degree F x ≠ 18 := by
  classical
  intro hx18
  apply no_degree_eighteen_of_high_neighbors_and_pair_degrees F x hu hlocal ?_ hx18
  intro y hy
  have hy20 : degree F y = 20 := (Finset.mem_filter.mp hy).2
  have hyx : y ≠ x := by
    intro heq
    subst y
    omega
  simpa [upperStar,Finset.pair_comm] using
    Erdos20V8DesignCounts.degree_twenty_pair_codegree_zero_or_five F hu hf y x hyx hy20

end Erdos20V8HighDegrees
