import SunflowerLean.Erdos20SharpTriples
import SunflowerLean.Erdos20ExtremalStructure

namespace Erdos20V11DegreeSeventeen
open Erdos20BCWConditional Erdos20RankThree Erdos20SharpTriples

/-- A seventeen-member triple family with eight disjoint partners per member
is exactly the disjoint-support union of intersecting families of sizes eight
and nine. No extension to an extremal ten-member design is assumed. -/
theorem triple_seventeen_min_disjoint_eight_decomposition
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hc : F.card = 17)
    (hd : ∀ S ∈ F, 8 ≤ (exactTrace F S ∅).card) :
    ∃ A B : Finset (Finset α), F = A ∪ B ∧ A.card = 8 ∧ B.card = 9 ∧
      Disjoint (support A) (support B) ∧
      (∀ S ∈ A, ∀ T ∈ A, (S ∩ T).Nonempty) ∧
      (∀ S ∈ B, ∀ T ∈ B, (S ∩ T).Nonempty) := by
  classical
  have hne : F.Nonempty := Finset.card_pos.mp (by omega)
  letI : Nonempty F := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  have hmin : 8 ≤ (disjointnessGraph F).minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro R
    rw [disjointnessGraph_degree_eq F hu R]
    exact hd R.val R.property
  have hcol : (disjointnessGraph F).Colorable 2 := by
    apply SimpleGraph.colorable_of_cliqueFree_lt_minDegree
      (disjointnessGraph_triangle_free F hf)
    have hcard : Fintype.card F = 17 := by simpa using hc
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
  have hsum : (classes 0).card + (classes 1).card = 17 := by
    rw [← Finset.card_union_of_disjoint hdis, ← hcover, hc]
  have hnon : ∀ i : Fin 2, (classes i).Nonempty := by
    intro i
    have h0 := hcap 0
    have h1 := hcap 1
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · exact Finset.card_pos.mp (by omega)
    · exact Finset.card_pos.mp (by omega)
  have hneigh : ∀ i j : Fin 2, i ≠ j → ∀ S ∈ classes i,
      exactTrace F S ∅ ⊆ classes j := by
    intro i j hij S hS T hT
    have hTF : T ∈ F := (Finset.mem_filter.mp hT).1
    have hTS : T ∩ S = ∅ := (Finset.mem_filter.mp hT).2
    have hn : T ∉ classes i := by
      intro hTi
      have hN := hinter i T hTi S hS
      simpa [hTS] using hN
    have hcT : c ⟨T,hTF⟩ = j := by
      have hcTi : c ⟨T,hTF⟩ ≠ i := by
        intro he
        exact hn ((hmem i T).mpr ⟨hTF,he⟩)
      omega
    exact (hmem j T).mpr ⟨hTF,hcT⟩
  have hlow0 : 8 ≤ (classes 0).card := by
    obtain ⟨S,hS⟩ := hnon 1
    exact (hd S (hsub 1 hS)).trans
      (Finset.card_le_card (hneigh 1 0 (by decide) S hS))
  have hlow1 : 8 ≤ (classes 1).card := by
    obtain ⟨S,hS⟩ := hnon 0
    exact (hd S (hsub 0 hS)).trans
      (Finset.card_le_card (hneigh 0 1 (by decide) S hS))
  have hsplit : (classes 0).card = 8 ∨ (classes 1).card = 8 := by omega
  have hbuild : ∀ i j : Fin 2, i ≠ j → (classes i).card = 8 →
      (classes j).card = 9 → F = classes i ∪ classes j →
      Disjoint (support (classes i)) (support (classes j)) := by
    intro i j hij hi hj hcov
    have hcross : ∀ S ∈ classes i, ∀ T ∈ classes j, S ∩ T = ∅ := by
      intro S hS T hT
      have hsubset := hneigh j i (Ne.symm hij) T hT
      have heq : exactTrace F T ∅ = classes i := by
        apply Finset.eq_of_subset_of_card_le hsubset
        rw [hi]
        exact hd T (hsub j hT)
      have hm : S ∈ exactTrace F T ∅ := by rw [heq]; exact hS
      exact (Finset.mem_filter.mp hm).2
    apply Finset.disjoint_left.mpr
    intro x hxA hxB
    obtain ⟨S,hS,hxS⟩ := Finset.mem_biUnion.mp hxA
    obtain ⟨T,hT,hxT⟩ := Finset.mem_biUnion.mp hxB
    have hI : x ∈ S ∩ T := Finset.mem_inter.mpr ⟨hxS,hxT⟩
    rw [hcross S hS T hT] at hI
    exact Finset.notMem_empty x hI
  rcases hsplit with h0 | h1
  · have h1 : (classes 1).card = 9 := by omega
    exact ⟨classes 0,classes 1,hcover,h0,h1,
      hbuild 0 1 (by decide) h0 h1 hcover,hinter 0,hinter 1⟩
  · have h0 : (classes 0).card = 9 := by omega
    have hcov : F = classes 1 ∪ classes 0 := by simpa [Finset.union_comm] using hcover
    exact ⟨classes 1,classes 0,hcov,h1,h0,
      hbuild 1 0 (by decide) h1 h0 hcov,hinter 1,hinter 0⟩

end Erdos20V11DegreeSeventeen
