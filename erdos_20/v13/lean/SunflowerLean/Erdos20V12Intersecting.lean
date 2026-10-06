import SunflowerLean.Erdos20V12Nineteen
import SunflowerLean.Erdos20V9HighCompatibility

namespace Erdos20V12Intersecting
open Erdos20BCWConditional Erdos20StrictCore Erdos20RankThreeEven
open Erdos20V12Nineteen Erdos20V8Intersecting Erdos20DegreeCongruences

/-- Nineteen triples with a four-point transversal must have a point of degree
six. A missing near-extremal classification is not assumed. -/
theorem nineteen_transversal_four_has_degree_six
    {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hu : ∀ P ∈ L, P.card=3) (hf : IsSunflowerFree L 3) (hc : L.card=19)
    (C : Finset α) (hC : C.card≤4)
    (hhit : ∀ P ∈ L, (P ∩ C).Nonempty) :
    ∃ y, (L.filter (fun P => y ∈ P)).card=6 := by
  by_contra hn
  push_neg at hn
  apply nineteen_max_degree_five_no_transversal_four L hu hf hc ?_ C hC hhit
  intro y
  have hb := rank_three_degree_le_six L hu hf y
  have he := hn y
  omega

/-- In an intersecting rank-four family of at least twenty members, every
point of degree nineteen lies in a pair of codegree six. -/
theorem intersecting_degree_nineteen_has_pair_six
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (hi : ∀ R ∈ F, ∀ S ∈ F, (R ∩ S).Nonempty) (hc : 20≤F.card)
    (x : α) (hx : degree F x=19) :
    ∃ y, x≠y ∧ (upperStar F {x,y}).card=6 := by
  classical
  have hex : ∃ R ∈ F, x ∉ R := by
    by_contra hn
    push_neg at hn
    have he : F.filter (fun R => x ∈ R)=F := Finset.filter_eq_self.mpr hn
    change (F.filter (fun R => x ∈ R)).card=19 at hx
    rw [he] at hx
    omega
  obtain ⟨R,hR,hxR⟩ := hex
  have hLu : ∀ P ∈ residualLink F {x}, P.card=3 := by
    simpa using residualLink_uniform (core := ({x} : Finset α)) hu
  have hLc : (residualLink F {x}).card=19 := by
    simpa [card_residualLink,upperStar,degree] using hx
  obtain ⟨y,hy⟩ := nineteen_transversal_four_has_degree_six _ hLu
    (residualLink_sunflowerFree hf) hLc R (by rw [hu R hR])
    (avoiding_member_hits_point_link F x R hi hR hxR)
  have hxy : x≠y := by
    intro he
    subst y
    have hz : (residualLink F {x}).filter (fun P => x∈P)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro P hP
      obtain ⟨hP,hxP⟩ := Finset.mem_filter.mp hP
      exact Erdos20V9HighCompatibility.point_not_mem_residue F x P hP hxP
    rw [hz] at hy
    simp at hy
  refine ⟨y,hxy,?_⟩
  have he := card_filter_residualLink F ({x} : Finset α) {y} (by simpa using hxy.symm)
  simp only [Finset.singleton_subset_iff,Finset.singleton_union] at he
  rw [he] at hy
  exact hy

end Erdos20V12Intersecting
