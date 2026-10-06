import SunflowerLean.Erdos20V11HighSupport

namespace Erdos20V11EdgeThird
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20ExtremalTwenty Erdos20V8DesignCounts

/-- An intersecting ten-design whose blocks meet a set in zero or two points
has support disjoint from that set. The first and second incidence moments
exclude every nonzero supported trace size. -/
theorem ten_zero_or_two_trace_support_disjoint {α : Type*} [DecidableEq α]
    (A : Finset (Finset α)) (hu : ∀ P ∈ A, P.card=3)
    (hf : IsSunflowerFree A 3) (hi : ∀ P ∈ A, ∀ Q ∈ A, (P ∩ Q).Nonempty)
    (hc : A.card=10) (U : Finset α)
    (ht : ∀ P ∈ A, (P ∩ U).card=0 ∨ (P ∩ U).card=2) :
    Disjoint (support A) U := by
  classical
  let C := U ∩ support A
  have he (P : Finset α) (hP : P ∈ A) : P ∩ C = P ∩ U := by
    ext u
    simp only [C,Finset.mem_inter]
    exact ⟨fun h => ⟨h.1,h.2.1⟩,fun h => ⟨h.1,h.2,member_subset_support hP h.1⟩⟩
  have hcap : ∀ P ∈ A, (P ∩ C).card ≤ 2 := by
    intro P hP
    rw [he P hP]
    rcases ht P hP with h | h <;> omega
  have h1 : blockCount A C 1=0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro P hP
    obtain ⟨hPA,hpc⟩ := Finset.mem_filter.mp hP
    rw [he P hPA] at hpc
    rcases ht P hPA with h | h <;> omega
  have hp := ten_design_block_counts A hu hf hi hc C Finset.inter_subset_right hcap
  have h0 : C.card=0 := by
    rcases hp with h | h | h | h <;> omega
  have hz : U ∩ support A=∅ := Finset.card_eq_zero.mp h0
  exact (Finset.disjoint_iff_inter_eq_empty.mpr hz).symm

/-- The same trace restriction excludes the whole support of an extremal
point link, by applying the ten-design moment argument to both components. -/
theorem twenty_zero_or_two_trace_support_disjoint {α : Type*} [DecidableEq α]
    (L : Finset (Finset α)) (hu : ∀ P ∈ L, P.card=3)
    (hf : IsSunflowerFree L 3) (hc : L.card=20) (U : Finset α)
    (ht : ∀ P ∈ L, (P ∩ U).card=0 ∨ (P ∩ U).card=2) :
    Disjoint (support L) U := by
  obtain ⟨A,B,hL,hdis,hpars⟩ := extremal_twenty_two_disjoint_designs L hu hf hc
  have hAL : A ⊆ L := by rw [hL]; exact Finset.subset_union_left
  have hBL : B ⊆ L := by rw [hL]; exact Finset.subset_union_right
  have ha := hpars A (by simp)
  have hb := hpars B (by simp)
  have hdA := ten_zero_or_two_trace_support_disjoint A (fun P hP => hu P (hAL hP))
    (fun J hJ hs => hf J (hJ.trans hAL) hs) ha.2.1 ha.1 U (fun P hP => ht P (hAL hP))
  have hdB := ten_zero_or_two_trace_support_disjoint B (fun P hP => hu P (hBL hP))
    (fun J hJ hs => hf J (hJ.trans hBL) hs) hb.2.1 hb.1 U (fun P hP => ht P (hBL hP))
  apply Finset.disjoint_left.mpr
  intro u huL huU
  obtain ⟨P,hP,huP⟩ := Finset.mem_biUnion.mp huL
  rw [hL] at hP
  rcases Finset.mem_union.mp hP with hPA | hPB
  · exact Finset.disjoint_left.mp hdA (member_subset_support hPA huP) huU
  · exact Finset.disjoint_left.mp hdB (member_subset_support hPB huP) huU

end Erdos20V11EdgeThird
