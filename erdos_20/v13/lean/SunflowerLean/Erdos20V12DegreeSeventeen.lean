import SunflowerLean.Erdos20V12ProfileScoreBridge
import SunflowerLean.Erdos20V11Final

namespace Erdos20V12DegreeSeventeen
open Erdos20BCWConditional Erdos20StrictCore Erdos20RankThree Erdos20Incidence
open Erdos20DegreeCongruences Erdos20V8Global Erdos20V8Boundary Erdos20V8DesignCounts
open Erdos20V11DegreeSeventeen Erdos20V12Profile

/-- In the all-meeting-at-least-fifty-four regime no point has degree
seventeen. Its nine-member separated link component would be partitioned
into five-member high-point stars, forcing five to divide nine. -/
theorem all_meeting_fifty_four_degree_ne_seventeen
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (hm : ∀ R ∈ F, 54 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card)
    (x : α) : degree F x ≠ 17 := by
  classical
  intro hx
  let L := residualLink F {x}
  obtain ⟨A,B,hL,hA,hB,hsep,hiA,hiB⟩ :=
    degree_seventeen_link_eight_nine_decomposition F hu hf hm x hx
  have hAL : A ⊆ L := by change A ⊆ residualLink F {x}; rw [hL]; exact Finset.subset_union_left
  have hBL : B ⊆ L := by change B ⊆ residualLink F {x}; rw [hL]; exact Finset.subset_union_right
  have hxH : x ∉ highPoints F := by
    intro hh
    have hh20 := (Finset.mem_filter.mp hh).2
    omega
  let K := support B ∩ highPoints F
  have hcover : ∀ P ∈ B, (P ∩ K).card=1 := by
    intro P hP
    have hPL : P ∈ residualLink F {x} := hBL hP
    have hxP : x ∉ P := Erdos20V9HighCompatibility.point_not_mem_residue F x P hPL
    have hRP : insert x P ∈ F := by simpa using core_union_residual_mem_family hPL
    have hdiff : insert x P \ {x} = P := by
      ext u
      simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton]
      constructor
      · rintro ⟨he | hu,hne⟩
        · exact False.elim (hne he)
        · exact hu
      · intro hu
        exact ⟨Or.inr hu,fun he => hxP (he ▸ hu)⟩
    have htrace : (exactTrace F (insert x P) {x}).card=8 := by
      have he := singleton_residual_eq_empty_link_trace F (insert x P) x (by simp)
      have hc := congrArg Finset.card he
      rw [exact_trace_card_residual,hdiff] at hc
      rw [exact_disjoint_trace_of_separated_partition (residualLink F {x}) B A
        (by simpa [Finset.union_comm] using hL) hsep.symm hiB P hP,hA] at hc
      exact hc
    obtain ⟨y,hyR,hy20⟩ := meeting_fifty_four_low_score_high_companion F hu hf
      (insert x P) hRP (hm _ hRP) x (by simp) (by rw [hx,htrace])
    have hyx : y≠x := by intro he; subst y; omega
    have hyP : y ∈ P := (Finset.mem_insert.mp hyR).resolve_left hyx
    have hyH : y ∈ highPoints F := Finset.mem_filter.mpr
      ⟨member_subset_support hRP hyR,hy20⟩
    have hyK : y ∈ K := Finset.mem_inter.mpr ⟨member_subset_support hP hyP,hyH⟩
    have hlo : 0 < (P ∩ K).card := Finset.card_pos.mpr
      ⟨y,Finset.mem_inter.mpr ⟨hyP,hyK⟩⟩
    have hsub : P ∩ K ⊆ insert x P ∩ highPoints F := by
      intro y hy
      exact Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_inter.mp hy).1,
        (Finset.mem_inter.mp (Finset.mem_inter.mp hy).2).2⟩
    have hhi := (Finset.card_le_card hsub).trans
      (Erdos20V11Final.all_meeting_fifty_four_member_high_cap_one F hu hf hm _ hRP)
    omega
  have hdeg : ∀ y ∈ K, (B.filter (fun P => y ∈ P)).card=5 := by
    intro y hy
    obtain ⟨hyB,hyH⟩ := Finset.mem_inter.mp hy
    have hyx : y≠x := by intro he; exact hxH (he ▸ hyH)
    have hy20 : degree F y=20 := (Finset.mem_filter.mp hyH).2
    have hfilter : L.filter (fun P => y ∈ P) = B.filter (fun P => y ∈ P) := by
      ext P
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hPL,hyP⟩
        have hPB : P ∈ B := by
          change P ∈ residualLink F {x} at hPL
          rw [hL] at hPL
          rcases Finset.mem_union.mp hPL with hPA | hPB
          · exact False.elim (Finset.disjoint_left.mp hsep (member_subset_support hPA hyP) hyB)
          · exact hPB
        exact ⟨hPB,hyP⟩
      · rintro ⟨hPB,hyP⟩
        exact ⟨hBL hPB,hyP⟩
    have hpair := degree_twenty_pair_codegree_zero_or_five F hu hf y x hyx hy20
    have he := card_filter_residualLink F ({x} : Finset α) {y} (by simpa using hyx)
    simp only [Finset.singleton_subset_iff,Finset.singleton_union] at he
    have he' : (B.filter (fun P => y ∈ P)).card=(upperStar F {y,x}).card := by
      rw [← hfilter]
      simpa [L,Finset.pair_comm] using he
    obtain ⟨P,hPB,hyP⟩ := Finset.mem_biUnion.mp hyB
    have hpos : 0 < (B.filter (fun P => y ∈ P)).card :=
      Finset.card_pos.mpr ⟨P,Finset.mem_filter.mpr ⟨hPB,hyP⟩⟩
    omega
  have hsum : 5*K.card=9 := by
    calc
      _ = ∑ y ∈ K, (B.filter (fun P => y ∈ P)).card := by
        rw [show (∑ y ∈ K, (B.filter (fun P => y ∈ P)).card)=∑ _y ∈ K, 5 from
          Finset.sum_congr rfl (fun y hy => hdeg y hy)]
        simp [Nat.mul_comm]
      _ = ∑ P ∈ B, (P ∩ K).card := (incidence_sum_eq B K).symm
      _ = ∑ _P ∈ B, 1 := Finset.sum_congr rfl hcover
      _ = 9 := by simp [hB]
  omega

/-- Minimum supported degree improves to eighteen in the all-meeting54
regime. This statement has no I27 or cardinality81 assumption. -/
theorem all_meeting_fifty_four_min_degree_eighteen
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (hm : ∀ R ∈ F, 54 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card)
    (x : α) (hx : x ∈ support F) : 18 ≤ degree F x := by
  have hlo := Erdos20V10MinimumDegree.all_meeting_fifty_four_min_degree_seventeen F hu hf hm x hx
  have hne := all_meeting_fifty_four_degree_ne_seventeen F hu hf hm x
  omega

end Erdos20V12DegreeSeventeen
