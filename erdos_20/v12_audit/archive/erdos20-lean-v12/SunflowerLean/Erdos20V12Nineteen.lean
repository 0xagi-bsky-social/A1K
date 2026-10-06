import SunflowerLean.Erdos20ExtremalTwenty
import SunflowerLean.Erdos20V8Intersecting

namespace Erdos20V12Nineteen
open Erdos20BCWConditional Erdos20RankThree Erdos20ExtremalTwenty
open Erdos20Incidence Erdos20DesignSeparation Erdos20V8Intersecting Erdos20SharpTriples

/-- A nineteen-member triple family whose point degrees are at most five
contains an intersecting ten-member component. The degree premise is explicit. -/
theorem nineteen_max_degree_five_contains_ten
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card=3) (hf : IsSunflowerFree F 3) (hc : F.card=19)
    (hd : ∀ x, (F.filter (fun S => x ∈ S)).card≤5) :
    ∃ H ⊆ F, H.card=10 ∧ ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty := by
  classical
  have hne : F.Nonempty := Finset.card_pos.mp (by omega)
  letI : Nonempty F := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  have hbound (R : Finset α) (hR : R ∈ F) :
      (F.filter (fun S => (S ∩ R).Nonempty)).card≤11 := by
    have hdef := triple_meeting_incidence_defect F R hR (hu R hR)
    have hs := singleton_intersection_card_le_nine F R hR hu hf
    have hsum : (∑ x ∈ R, (F.filter (fun S => x ∈ S)).card) ≤ 15 := by
      calc
        _ ≤ ∑ _x ∈ R, 5 := Finset.sum_le_sum (fun x _ => hd x)
        _ = 15 := by simp [hu R hR]
    omega
  have hmin : 8 ≤ (disjointnessGraph F).minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro R
    rw [disjointnessGraph_degree_eq F hu R]
    have hb := hbound R.val R.property
    have hp := Finset.filter_card_add_filter_neg_card_eq_card
      (s := F) (p := fun S => (S ∩ R.val).Nonempty)
    simp only [Finset.not_nonempty_iff_eq_empty] at hp
    change 8 ≤ (F.filter (fun S => S ∩ R.val = ∅)).card
    omega
  have hcol : (disjointnessGraph F).Colorable 2 := by
    apply SimpleGraph.colorable_of_cliqueFree_lt_minDegree
      (disjointnessGraph_triangle_free F hf)
    have hcard : Fintype.card F = 19 := by simpa using hc
    simp only [hcard]
    omega
  obtain ⟨c⟩ := hcol
  let classes : Fin 2 → Finset (Finset α) := fun i =>
    (Finset.univ.filter (fun S : F => c S = i)).image Subtype.val
  have hmem : ∀ i S, S ∈ classes i ↔ ∃ hS : S ∈ F, c ⟨S,hS⟩ = i := by
    intro i S
    simp only [classes, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨T, hi, rfl⟩
      exact ⟨T.property, hi⟩
    · rintro ⟨hS, hi⟩
      exact ⟨⟨S,hS⟩, hi, rfl⟩
  have hsub : ∀ i, classes i ⊆ F := by
    intro i S hS
    exact ((hmem i S).mp hS).choose
  have hinter : ∀ i, ∀ S ∈ classes i, ∀ T ∈ classes i, (S ∩ T).Nonempty := by
    intro i S hS T hT
    obtain ⟨hSF, hcS⟩ := (hmem i S).mp hS
    obtain ⟨hTF, hcT⟩ := (hmem i T).mp hT
    by_contra hnot
    have hi : S ∩ T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    have hneq : (⟨S,hSF⟩ : F) ≠ ⟨T,hTF⟩ := by
      intro heq
      have hv : S = T := congrArg Subtype.val heq
      have he : S = ∅ := by simpa [← hv] using hi
      have hs3 := hu S hSF
      simp [he] at hs3
    exact c.valid (show (disjointnessGraph F).Adj ⟨S,hSF⟩ ⟨T,hTF⟩ from ⟨hneq,hi⟩)
      (hcS.trans hcT.symm)
  have hcap : ∀ i, (classes i).card ≤ 10 := by
    intro i
    exact intersecting_rank_three_card_le_ten _
      (fun S hS => hu S (hsub i hS))
      (fun H hH hsun => hf H (hH.trans (hsub i)) hsun) (hinter i)
  have hcover : F = classes 0 ∪ classes 1 := by
    apply Finset.Subset.antisymm
    · intro S hS
      have hi : c ⟨S,hS⟩ = 0 ∨ c ⟨S,hS⟩ = 1 := by omega
      rcases hi with hi | hi
      · exact Finset.mem_union_left _ ((hmem 0 S).mpr ⟨hS,hi⟩)
      · exact Finset.mem_union_right _ ((hmem 1 S).mpr ⟨hS,hi⟩)
    · exact Finset.union_subset (hsub 0) (hsub 1)
  have hdis : Disjoint (classes 0) (classes 1) := by
    apply Finset.disjoint_left.mpr
    intro S hS hT
    obtain ⟨hSF,hcS⟩ := (hmem 0 S).mp hS
    obtain ⟨hTF,hcT⟩ := (hmem 1 S).mp hT
    have he : (0 : Fin 2) = 1 := hcS.symm.trans hcT
    exact (by decide : (0 : Fin 2) ≠ 1) he
  have hsum : (classes 0).card + (classes 1).card = 19 := by
    rw [← Finset.card_union_of_disjoint hdis, ← hcover, hc]
  have h0 := hcap 0
  have h1 := hcap 1
  by_cases he : (classes 0).card=10
  · exact ⟨classes 0,hsub 0,he,hinter 0⟩
  · exact ⟨classes 1,hsub 1,by omega,hinter 1⟩

/-- Nineteen triples of maximum point degree five split as a ten-design and
an intersecting nine-member component on disjoint supports. The nine-component
is not assumed to extend to a ten-design. -/
theorem nineteen_max_degree_five_decomposition
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card=3) (hf : IsSunflowerFree F 3) (hc : F.card=19)
    (hd : ∀ x, (F.filter (fun S => x ∈ S)).card≤5) :
    ∃ H K : Finset (Finset α), F=H ∪ K ∧ H.card=10 ∧ K.card=9 ∧
      Disjoint (support H) (support K) ∧
      (∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty) ∧
      (∀ S ∈ K, ∀ T ∈ K, (S ∩ T).Nonempty) := by
  obtain ⟨H,hHF,hHc,hHi⟩ := nineteen_max_degree_five_contains_ten F hu hf hc hd
  refine ⟨H,F \ H,(Finset.union_sdiff_of_subset hHF).symm,hHc,?_,
    intersecting_ten_complement_supports_disjoint F H hu hf hHF hHi hHc,hHi,
    complement_of_intersecting_ten_intersecting F H hu hf hHF hHi hHc⟩
  rw [Finset.card_sdiff_of_subset hHF,hc,hHc]

/-- A four-point transversal is impossible in a nineteen-member triple family
of maximum degree five. This avoids any classification of the nine-component. -/
theorem nineteen_max_degree_five_no_transversal_four
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card=3) (hf : IsSunflowerFree F 3) (hc : F.card=19)
    (hd : ∀ x, (F.filter (fun S => x ∈ S)).card≤5)
    (C : Finset α) (hC : C.card≤4) (hhit : ∀ S ∈ F, (S ∩ C).Nonempty) : False := by
  obtain ⟨H,hHF,hHc,hHi⟩ := nineteen_max_degree_five_contains_ten F hu hf hc hd
  have hb := triples_with_ten_design_transversal_four_card_le_sixteen
    F H C hu hf hHF hHi hHc hC hhit
  omega

end Erdos20V12Nineteen
