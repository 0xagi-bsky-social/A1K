import SunflowerLean.Erdos20ExtremalStructure

namespace Erdos20TracePatterns
open Erdos20RankThree Erdos20ExtremalStructure Erdos20BCWConditional

private theorem split_card {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (p q : Finset α → Prop) [DecidablePred p] [DecidablePred q] :
    (F.filter p).card = (F.filter (fun S => p S ∧ q S)).card +
      (F.filter (fun S => p S ∧ ¬ q S)).card := by
  simpa [Finset.filter_filter] using
    (Finset.filter_card_add_filter_neg_card_eq_card (s := F.filter p) (p := q)).symm

/-- Exact trace counts on a three-point anchor recover its size and point degrees. -/
theorem trace_count_equations {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hR : {a,b,c} ∈ F) (hu : ∀ S ∈ F, S.card = 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) :
    let n := fun C => (exactTrace F {a,b,c} C).card
    F.card = 1 + n {a} + n {b} + n {c} + n {b,c} + n {a,c} + n {a,b} ∧
    (F.filter (fun S => a ∈ S)).card = 1 + n {a} + n {a,c} + n {a,b} ∧
    (F.filter (fun S => b ∈ S)).card = 1 + n {b} + n {b,c} + n {a,b} ∧
    (F.filter (fun S => c ∈ S)).card = 1 + n {c} + n {b,c} + n {a,c} := by
  classical
  have e000 : F.filter (fun S => a ∉ S ∧ b ∉ S ∧ c ∉ S) = exactTrace F {a,b,c} ∅ := by
    ext S
    simp only [exactTrace, Finset.mem_filter]
    apply and_congr_right
    intro _
    constructor
    · intro h
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
      aesop
    · intro h
      have ha := congrArg (fun T => a ∈ T) h
      have hb := congrArg (fun T => b ∈ T) h
      have hc := congrArg (fun T => c ∈ T) h
      simp [hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc] at ha hb hc
      tauto
  have e001 : F.filter (fun S => a ∉ S ∧ b ∉ S ∧ c ∈ S) = exactTrace F {a,b,c} {c} := by
    ext S
    simp only [exactTrace, Finset.mem_filter]
    apply and_congr_right
    intro _
    constructor
    · intro h
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton ]
      aesop
    · intro h
      have ha := congrArg (fun T => a ∈ T) h
      have hb := congrArg (fun T => b ∈ T) h
      have hc := congrArg (fun T => c ∈ T) h
      simp [hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc] at ha hb hc
      tauto
  have e010 : F.filter (fun S => a ∉ S ∧ b ∈ S ∧ c ∉ S) = exactTrace F {a,b,c} {b} := by
    ext S
    simp only [exactTrace, Finset.mem_filter]
    apply and_congr_right
    intro _
    constructor
    · intro h
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton ]
      aesop
    · intro h
      have ha := congrArg (fun T => a ∈ T) h
      have hb := congrArg (fun T => b ∈ T) h
      have hc := congrArg (fun T => c ∈ T) h
      simp [hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc] at ha hb hc
      tauto
  have e011 : F.filter (fun S => a ∉ S ∧ b ∈ S ∧ c ∈ S) = exactTrace F {a,b,c} {b,c} := by
    ext S
    simp only [exactTrace, Finset.mem_filter]
    apply and_congr_right
    intro _
    constructor
    · intro h
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton ]
      aesop
    · intro h
      have ha := congrArg (fun T => a ∈ T) h
      have hb := congrArg (fun T => b ∈ T) h
      have hc := congrArg (fun T => c ∈ T) h
      simp [hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc] at ha hb hc
      tauto
  have e100 : F.filter (fun S => a ∈ S ∧ b ∉ S ∧ c ∉ S) = exactTrace F {a,b,c} {a} := by
    ext S
    simp only [exactTrace, Finset.mem_filter]
    apply and_congr_right
    intro _
    constructor
    · intro h
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton ]
      aesop
    · intro h
      have ha := congrArg (fun T => a ∈ T) h
      have hb := congrArg (fun T => b ∈ T) h
      have hc := congrArg (fun T => c ∈ T) h
      simp [hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc] at ha hb hc
      tauto
  have e101 : F.filter (fun S => a ∈ S ∧ b ∉ S ∧ c ∈ S) = exactTrace F {a,b,c} {a,c} := by
    ext S
    simp only [exactTrace, Finset.mem_filter]
    apply and_congr_right
    intro _
    constructor
    · intro h
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton ]
      aesop
    · intro h
      have ha := congrArg (fun T => a ∈ T) h
      have hb := congrArg (fun T => b ∈ T) h
      have hc := congrArg (fun T => c ∈ T) h
      simp [hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc] at ha hb hc
      tauto
  have e110 : F.filter (fun S => a ∈ S ∧ b ∈ S ∧ c ∉ S) = exactTrace F {a,b,c} {a,b} := by
    ext S
    simp only [exactTrace, Finset.mem_filter]
    apply and_congr_right
    intro _
    constructor
    · intro h
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton ]
      aesop
    · intro h
      have ha := congrArg (fun T => a ∈ T) h
      have hb := congrArg (fun T => b ∈ T) h
      have hc := congrArg (fun T => c ∈ T) h
      simp [hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc] at ha hb hc
      tauto
  have e111 : F.filter (fun S => a ∈ S ∧ b ∈ S ∧ c ∈ S) = exactTrace F {a,b,c} {a,b,c} := by
    ext S
    simp only [exactTrace, Finset.mem_filter]
    apply and_congr_right
    intro _
    constructor
    · intro h
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton ]
      aesop
    · intro h
      have ha := congrArg (fun T => a ∈ T) h
      have hb := congrArg (fun T => b ∈ T) h
      have hc := congrArg (fun T => c ∈ T) h
      simp [hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc] at ha hb hc
      tauto
  have e000c : (exactTrace F {a,b,c} ∅).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro S hS
    obtain ⟨hSF,he⟩ := Finset.mem_filter.mp hS
    have hn := hi S hSF {a,b,c} hR
    simp [he] at hn
  have e111c : (exactTrace F {a,b,c} {a,b,c}).card = 1 := by
    have he : exactTrace F {a,b,c} {a,b,c} = {{a,b,c}} := by
      ext S
      simp only [exactTrace, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hS,he⟩
        have hs : {a,b,c} ⊆ S := by rw [← he]; exact Finset.inter_subset_left
        exact (Finset.eq_of_subset_of_card_le hs (by rw [hu S hS]; simp [hab,hac,hbc])).symm
      · intro he
        subst S
        exact ⟨hR,Finset.inter_self _⟩
    simp [he]
  have s0 := Finset.filter_card_add_filter_neg_card_eq_card (s := F) (p := fun S => a ∈ S)
  have s1 := split_card F (fun S => a ∈ S) (fun S => b ∈ S)
  have s2 := split_card F (fun S => a ∉ S) (fun S => b ∈ S)
  have s3 := split_card F (fun S => a ∈ S ∧ b ∈ S) (fun S => c ∈ S)
  have s4 := split_card F (fun S => a ∈ S ∧ b ∉ S) (fun S => c ∈ S)
  have s5 := split_card F (fun S => a ∉ S ∧ b ∈ S) (fun S => c ∈ S)
  have s6 := split_card F (fun S => a ∉ S ∧ b ∉ S) (fun S => c ∈ S)
  have sb := split_card F (fun S => b ∈ S) (fun S => a ∈ S)
  have sc := split_card F (fun S => c ∈ S) (fun S => a ∈ S)
  have sc1 := split_card F (fun S => c ∈ S ∧ a ∈ S) (fun S => b ∈ S)
  have sc2 := split_card F (fun S => c ∈ S ∧ a ∉ S) (fun S => b ∈ S)
  simp only [and_assoc] at s3 s4 s5 s6
  simp only [and_comm, and_left_comm] at sb sc sc1 sc2
  simp only [e000,e001,e010,e011,e100,e101,e110,e111,e000c,e111c] at *
  omega

set_option maxHeartbeats 1000000 in
/-- Saturation of the three opposite trace inequalities permits only local degrees
444, 355 (up to order), or 555. -/
theorem intersecting_ten_member_degree_pattern {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 10)
    (R : Finset α) (hR : R ∈ F) : MemberDegreePattern F R := by
  classical
  obtain ⟨a,b,c,hab,hac,hbc,hshape⟩ := Finset.card_eq_three.mp (hu R hR)
  subst R
  obtain ⟨hsize,hda,hdb,hdc⟩ := trace_count_equations F a b c hab hac hbc hR hu hi
  dsimp only at hsize hda hdb hdc
  have hpa := opposite_traces_sum_le_three F {a,b,c} a hR (by simp) hu hf hi
  have hpb := opposite_traces_sum_le_three F {a,b,c} b hR (by simp) hu hf hi
  have hpc := opposite_traces_sum_le_three F {a,b,c} c hR (by simp) hu hf hi
  have hea : ({a,b,c} : Finset α).erase a = {b,c} := by simp [hab,hac]
  have heb : ({a,b,c} : Finset α).erase b = {a,c} := by ext x; simp only [Finset.mem_erase,Finset.mem_insert,Finset.mem_singleton]; aesop
  have hec : ({a,b,c} : Finset α).erase c = {a,b} := by ext x; simp only [Finset.mem_erase,Finset.mem_insert,Finset.mem_singleton]; aesop
  simp only [hea,heb,hec] at hpa hpb hpc
  have hqa := pair_trace_card_le_one F {a,b,c} {b,c} hR hu hf (by simp) (by simp [hbc])
  have hqb := pair_trace_card_le_one F {a,b,c} {a,c} hR hu hf (by simp) (by simp [hac])
  have hqc := pair_trace_card_le_one F {a,b,c} {a,b} hR hu hf (by simp) (by simp [hab])
  have hA := intersecting_ten_degree_le_five F hu hf hi hc a
  have hB := intersecting_ten_degree_le_five F hu hf hi hc b
  have hC := intersecting_ten_degree_le_five F hu hf hi hc c
  have hp :
    ((F.filter (fun S => a ∈ S)).card = 4 ∧ (F.filter (fun S => b ∈ S)).card = 4 ∧ (F.filter (fun S => c ∈ S)).card = 4) ∨
    ((F.filter (fun S => a ∈ S)).card = 3 ∧ (F.filter (fun S => b ∈ S)).card = 5 ∧ (F.filter (fun S => c ∈ S)).card = 5) ∨
    ((F.filter (fun S => a ∈ S)).card = 5 ∧ (F.filter (fun S => b ∈ S)).card = 3 ∧ (F.filter (fun S => c ∈ S)).card = 5) ∨
    ((F.filter (fun S => a ∈ S)).card = 5 ∧ (F.filter (fun S => b ∈ S)).card = 5 ∧ (F.filter (fun S => c ∈ S)).card = 3) ∨
    ((F.filter (fun S => a ∈ S)).card = 5 ∧ (F.filter (fun S => b ∈ S)).card = 5 ∧ (F.filter (fun S => c ∈ S)).card = 5) := by
    interval_cases hqa0 : (exactTrace F {a,b,c} {b,c}).card <;>
      interval_cases hqb0 : (exactTrace F {a,b,c} {a,c}).card <;>
      interval_cases hqc0 : (exactTrace F {a,b,c} {a,b}).card <;> omega
  rcases hp with ⟨ha,hb,hc'⟩ | ⟨ha,hb,hc'⟩ | ⟨ha,hb,hc'⟩ | ⟨ha,hb,hc'⟩ | ⟨ha,hb,hc'⟩ <;>
    simp [MemberDegreePattern,Finset.filter_insert,Finset.filter_singleton,ha,hb,hc']

/-- Every intersecting ten-member sunflower-free triple family is regular on exactly six points. -/
theorem intersecting_ten_regular_six_support {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 10) :
    (support F).card = 6 ∧ ∀ x ∈ support F, (F.filter (fun T => x ∈ T)).card = 5 :=
  local_patterns_force_regular_six_support F hu hi hc
    (intersecting_ten_member_degree_pattern F hu hf hi hc)

end Erdos20TracePatterns
