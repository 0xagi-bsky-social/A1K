import SunflowerLean.Erdos20V12Intersecting
import SunflowerLean.Erdos20GraphEquality

namespace Erdos20V13Intersecting
open Erdos20BCWConditional Erdos20StrictCore Erdos20DegreeCongruences
open Erdos20V12Intersecting Erdos20GraphEquality

/-- Literal inclusion-exclusion for the original point stars. -/
theorem star_union_card_add_pair_codegree
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x y : α) :
    ((F.filter (fun S => x ∈ S)) ∪ (F.filter (fun S => y ∈ S))).card +
      (upperStar F {x,y}).card = degree F x + degree F y := by
  classical
  have he : (F.filter (fun S => x ∈ S)) ∩ (F.filter (fun S => y ∈ S)) =
      upperStar F {x,y} := by
    ext S
    simp only [Finset.mem_inter, Finset.mem_filter, upperStar,
      Finset.insert_subset_iff, Finset.singleton_subset_iff]
    tauto
  simpa only [he,degree] using Finset.card_union_add_card_inter
    (F.filter (fun S => x ∈ S)) (F.filter (fun S => y ∈ S))

/-- The six-codegree partner lies between six and |F|-13 in degree.
The additive form avoids truncated natural-number subtraction. -/
theorem degree_nineteen_pair_six_partner_bounds
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x y : α)
    (hx : degree F x=19) (hxy : (upperStar F {x,y}).card=6) :
    6 ≤ degree F y ∧ degree F y + 13 ≤ F.card := by
  classical
  have hsub : upperStar F {x,y} ⊆ F.filter (fun S => y ∈ S) := by
    intro S hS
    obtain ⟨hSF,hpair⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr ⟨hSF,hpair (by simp)⟩
  have hlo := Finset.card_le_card hsub
  have hhi := Finset.card_le_card
    (Finset.union_subset (Finset.filter_subset (fun S => x ∈ S) F)
      (Finset.filter_subset (fun S => y ∈ S) F))
  have he := star_union_card_add_pair_codegree F x y
  change (upperStar F {x,y}).card ≤ degree F y at hlo
  rw [hx,hxy] at he
  rw [hxy] at hlo
  constructor <;> omega

/-- A degree-nineteen point in a 28-member intersecting rank-four family
has a distinct codegree-six partner of degree between six and fifteen. -/
theorem intersecting_twenty_eight_degree_nineteen_partner_bounds
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (hi : ∀ R ∈ F, ∀ S ∈ F, (R ∩ S).Nonempty) (hc : F.card=28)
    (x : α) (hx : degree F x=19) :
    ∃ y, x≠y ∧ (upperStar F {x,y}).card=6 ∧
      6 ≤ degree F y ∧ degree F y ≤ 15 := by
  obtain ⟨y,hne,hy⟩ := intersecting_degree_nineteen_has_pair_six F hu hf hi (by omega) x hx
  obtain ⟨hlo,hhi⟩ := degree_nineteen_pair_six_partner_bounds F x y hx hy
  exact ⟨y,hne,hy,hlo,by omega⟩

/-- Restoring the core recovers precisely the original star. -/
theorem upperStar_eq_image_restore_core
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (core : Finset α) :
    upperStar F core = (residualLink F core).image (fun P => core ∪ P) := by
  classical
  ext S
  constructor
  · intro hS
    obtain ⟨hSF,hcore⟩ := Finset.mem_filter.mp hS
    refine Finset.mem_image.mpr ⟨S \ core, mem_residualLink_iff.mpr ⟨S,hSF,hcore,rfl⟩, ?_⟩
    exact Finset.union_sdiff_of_subset hcore
  · intro hS
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨S,hSF,hcore,rfl⟩ := mem_residualLink_iff.mp hP
    rw [Finset.union_sdiff_of_subset hcore]
    exact Finset.mem_filter.mpr ⟨hSF,hcore⟩

/-- A six-codegree pair has exactly six original members: its core adjoined
to the edges of two disjoint triangles. The six residual vertices are all
outside the core, and are distinct within and between their triangles. -/
theorem pair_codegree_six_exact_two_triangles
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x y : α)
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (hxy : x ≠ y) (hc : (upperStar F {x,y}).card=6) :
    ∃ a b c d e f : α,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ d ≠ e ∧ d ≠ f ∧ e ≠ f ∧
      Disjoint ({a,b,c} : Finset α) {d,e,f} ∧
      Disjoint ({x,y} : Finset α) {a,b,c,d,e,f} ∧
      residualLink F {x,y} = {{a,b},{a,c},{b,c}} ∪ {{d,e},{d,f},{e,f}} ∧
      upperStar F {x,y} =
        (({{a,b},{a,c},{b,c}} ∪ {{d,e},{d,f},{e,f}}) : Finset (Finset α)).image (fun P => {x,y} ∪ P) := by
  classical
  have hul : ∀ P ∈ residualLink F {x,y}, P.card=2 := by
    simpa [Finset.card_pair hxy] using residualLink_uniform (core := ({x,y} : Finset α)) hu
  have hcl : (residualLink F {x,y}).card=6 := by rw [card_residualLink,hc]
  obtain ⟨a,b,c,d,e,f,hab,hac,hbc,hde,hdf,hef,hdis,hshape⟩ :=
    six_edges_two_disjoint_triangles (residualLink F {x,y}) hul
      (residualLink_sunflowerFree hf) hcl
  have hout : ∀ P ∈ residualLink F {x,y}, Disjoint ({x,y} : Finset α) P := by
    intro P hP
    exact residualLink_member_disjoint_core hP
  have hall : Disjoint ({x,y} : Finset α) {a,b,c,d,e,f} := by
    apply Finset.disjoint_left.mpr
    intro z hz hzm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzm
    rcases hzm with he | he | he | he | he | he
    · exact Finset.disjoint_left.mp (hout {a,b} (by simp [hshape])) hz (by simp [he])
    · exact Finset.disjoint_left.mp (hout {a,b} (by simp [hshape])) hz (by simp [he])
    · exact Finset.disjoint_left.mp (hout {a,c} (by simp [hshape])) hz (by simp [he])
    · exact Finset.disjoint_left.mp (hout {d,e} (by simp [hshape])) hz (by simp [he])
    · exact Finset.disjoint_left.mp (hout {d,e} (by simp [hshape])) hz (by simp [he])
    · exact Finset.disjoint_left.mp (hout {d,f} (by simp [hshape])) hz (by simp [he])
  refine ⟨a,b,c,d,e,f,hab,hac,hbc,hde,hdf,hef,hdis,hall,hshape,?_⟩
  rw [upperStar_eq_image_restore_core,hshape]

end Erdos20V13Intersecting

#print axioms Erdos20V13Intersecting.star_union_card_add_pair_codegree
#print axioms Erdos20V13Intersecting.degree_nineteen_pair_six_partner_bounds
#print axioms Erdos20V13Intersecting.intersecting_twenty_eight_degree_nineteen_partner_bounds
#print axioms Erdos20V13Intersecting.upperStar_eq_image_restore_core
#print axioms Erdos20V13Intersecting.pair_codegree_six_exact_two_triangles
