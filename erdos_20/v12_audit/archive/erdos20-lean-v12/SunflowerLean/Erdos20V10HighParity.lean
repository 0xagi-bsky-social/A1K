import SunflowerLean.Erdos20V9HighGraph
import SunflowerLean.Erdos20V9HighCompatibilityMain

/-! Exact parity of double-high members in a low point star. -/
namespace Erdos20V10HighParity
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20V8DesignCounts Erdos20V8Boundary Erdos20DegreeCongruences
open Erdos20ExtremalTwenty Erdos20V9HighGraph Erdos20V9HighCompatibility

/-- A pair in an extremal twenty-link belongs either to no blocks or to exactly
two blocks, because any nonempty pair fiber lies in one ten-design component. -/
theorem twenty_link_pair_codegree_zero_or_two
    {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hu : ∀ R ∈ L, R.card = 3) (hf : IsSunflowerFree L 3) (hc : L.card = 20)
    (x y : α) (hxy : x ≠ y) :
    (L.filter (fun R => ({x,y} : Finset α) ⊆ R)).card = 0 ∨
    (L.filter (fun R => ({x,y} : Finset α) ⊆ R)).card = 2 := by
  classical
  by_cases hne : (L.filter (fun R => ({x,y} : Finset α) ⊆ R)).Nonempty
  · obtain ⟨R,hR⟩ := hne
    obtain ⟨hRL,hxyR⟩ := Finset.mem_filter.mp hR
    have hxR : x ∈ R := hxyR (by simp)
    have hyR : y ∈ R := hxyR (by simp)
    obtain ⟨A,B,hL,hdis,hpars⟩ := extremal_twenty_two_disjoint_designs L hu hf hc
    have one_component (A B : Finset (Finset α)) (hL : L = A ∪ B)
        (hdis : Disjoint (support A) (support B)) (hRA : R ∈ A)
        (hpair : ∀ x ∈ support A, ∀ y ∈ support A, x ≠ y →
          (A.filter (fun S => ({x,y} : Finset α) ⊆ S)).card = 2) :
        (L.filter (fun S => ({x,y} : Finset α) ⊆ S)).card = 2 := by
      have he : L.filter (fun S => ({x,y} : Finset α) ⊆ S) =
          A.filter (fun S => ({x,y} : Finset α) ⊆ S) := by
        ext S
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hSL,hp⟩
          rw [hL] at hSL
          rcases Finset.mem_union.mp hSL with hSA | hSB
          · exact ⟨hSA,hp⟩
          · exact False.elim (Finset.disjoint_left.mp hdis
              (member_subset_support hRA hxR)
              (member_subset_support hSB (hp (by simp))))
        · rintro ⟨hSA,hp⟩
          exact ⟨by rw [hL]; exact Finset.mem_union_left _ hSA,hp⟩
      rw [he]
      exact hpair x (member_subset_support hRA hxR) y
        (member_subset_support hRA hyR) hxy
    right
    rw [hL] at hRL
    rcases Finset.mem_union.mp hRL with hRA | hRB
    · exact one_component A B hL hdis hRA (hpars A (by simp)).2.2.2.2
    · exact one_component B A (by rw [hL,Finset.union_comm]) hdis.symm hRB
        (hpars B (by simp)).2.2.2.2
  · exact Or.inl (Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne))

/-- Every three-point star containing a degree-twenty point has even size,
indeed size zero or two, when its three points are distinct. -/
theorem degree_twenty_triple_codegree_zero_or_two
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (y x z : α) (hyx : y ≠ x) (hyz : y ≠ z) (hxz : x ≠ z)
    (hy : y ∈ highPoints F) :
    (upperStar F {y,x,z}).card = 0 ∨ (upperStar F {y,x,z}).card = 2 := by
  let L := residualLink F {y}
  have huL : ∀ P ∈ L, P.card = 3 := by
    simpa using residualLink_uniform (core := ({y} : Finset α)) hu
  have hfL : IsSunflowerFree L 3 := residualLink_sunflowerFree hf
  have hcL : L.card = 20 := by
    simpa [L,card_residualLink,upperStar,degree] using (Finset.mem_filter.mp hy).2
  have hdis : Disjoint ({y} : Finset α) {x,z} := by simp [Ne.symm hyx,Ne.symm hyz]
  have he := card_filter_residualLink F ({y} : Finset α) {x,z} hdis
  simp only [Finset.singleton_union] at he
  have hp := twenty_link_pair_codegree_zero_or_two L huL hfL hcL x z hxz
  simpa only [L,he] using hp

end Erdos20V10HighParity
