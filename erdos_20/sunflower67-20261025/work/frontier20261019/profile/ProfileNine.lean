import SunflowerLean.Erdos20TracePatterns
import SunflowerLean.Erdos20DegreeCongruences

namespace FrontierNine
open Erdos20BCWConditional Erdos20RankThree Erdos20TracePatterns
open Erdos20ExtremalStructure Erdos20DegreeCongruences Erdos20Incidence

set_option maxHeartbeats 2000000

/-- Exact arithmetic consequences of the nine-member opposite-trace ledger. -/
theorem nine_trace_ledger (a b c sa sb sc pa pb pc : ℕ)
    (hn : 9 = 1+sa+sb+sc+pa+pb+pc)
    (ha : a=1+sa+pb+pc) (hb : b=1+sb+pa+pc) (hc : c=1+sc+pa+pb)
    (hpa : pa≤1) (hpb : pb≤1) (hpc : pc≤1)
    (hsa : sa+pa≤3) (hsb : sb+pb≤3) (hsc : sc+pc≤3)
    (hA : a≤5) (hB : b≤5) (hC : c≤5) :
    (2≤a ∧ 2≤b ∧ 2≤c) ∧
    (a=2 → b=5 ∧ c=5 ∧ pb=0 ∧ pc=0 ∧ sa=1) ∧
    (a=2 ∨ b=2 ∨ c=2 ∨ a=4 ∨ b=4 ∨ c=4) ∧
    ((if a=5 then 1 else 0)+(if b=5 then 1 else 0)+(if c=5 then 1 else 0)≤2) ∧
    ((if a=3 then 1 else 0)+(if b=3 then 1 else 0)+(if c=3 then 1 else 0)≤1) := by
  interval_cases pa <;> interval_cases pb <;> interval_cases pc <;>
    split_ifs <;> omega

/-- The arithmetic ledger is derived from actual family traces. -/
theorem nine_member_ordered_ledger {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S∈F, S.card=3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S∈F, ∀ T∈F, (S∩T).Nonempty) (hn : F.card=9)
    (a b c : α) (hab : a≠b) (hac : a≠c) (hbc : b≠c) (hR : {a,b,c}∈F) :
    (2≤degree F a ∧ 2≤degree F b ∧ 2≤degree F c) ∧
    (degree F a=2 → degree F b=5 ∧ degree F c=5 ∧
      (exactTrace F {a,b,c} {a,c}).card=0 ∧
      (exactTrace F {a,b,c} {a,b}).card=0 ∧
      (exactTrace F {a,b,c} {a}).card=1) ∧
    (degree F a=2 ∨ degree F b=2 ∨ degree F c=2 ∨
      degree F a=4 ∨ degree F b=4 ∨ degree F c=4) ∧
    ((if degree F a=5 then 1 else 0)+(if degree F b=5 then 1 else 0)+
      (if degree F c=5 then 1 else 0)≤2) ∧
    ((if degree F a=3 then 1 else 0)+(if degree F b=3 then 1 else 0)+
      (if degree F c=3 then 1 else 0)≤1) := by
  classical
  obtain ⟨hsize,hda,hdb,hdc⟩ := trace_count_equations F a b c hab hac hbc hR hu hi
  dsimp only at hsize hda hdb hdc
  have hpa := opposite_traces_sum_le_three F {a,b,c} a hR (by simp) hu hf hi
  have hpb := opposite_traces_sum_le_three F {a,b,c} b hR (by simp) hu hf hi
  have hpc := opposite_traces_sum_le_three F {a,b,c} c hR (by simp) hu hf hi
  have hea : ({a,b,c} : Finset α).erase a = {b,c} := by simp [hab,hac]
  have heb : ({a,b,c} : Finset α).erase b = {a,c} := by
    ext x
    simp only [Finset.mem_erase,Finset.mem_insert,Finset.mem_singleton]
    aesop
  have hec : ({a,b,c} : Finset α).erase c = {a,b} := by
    ext x
    simp only [Finset.mem_erase,Finset.mem_insert,Finset.mem_singleton]
    aesop
  simp only [hea,heb,hec] at hpa hpb hpc
  have hqa := pair_trace_card_le_one F {a,b,c} {b,c} hR hu hf (by simp) (by simp [hbc])
  have hqb := pair_trace_card_le_one F {a,b,c} {a,c} hR hu hf (by simp) (by simp [hac])
  have hqc := pair_trace_card_le_one F {a,b,c} {a,b} hR hu hf (by simp) (by simp [hab])
  have hA := intersecting_card_ge_seven_degree_le_five F hu hf hi (by omega) a
  have hB := intersecting_card_ge_seven_degree_le_five F hu hf hi (by omega) b
  have hC := intersecting_card_ge_seven_degree_le_five F hu hf hi (by omega) c
  apply nine_trace_ledger _ _ _
    (exactTrace F {a,b,c} {a}).card (exactTrace F {a,b,c} {b}).card
    (exactTrace F {a,b,c} {c}).card (exactTrace F {a,b,c} {b,c}).card
    (exactTrace F {a,b,c} {a,c}).card (exactTrace F {a,b,c} {a,b}).card
  · simpa [hn] using hsize
  · exact hda
  · exact hdb
  · exact hdc
  · exact hqa
  · exact hqb
  · exact hqc
  · exact hpa
  · exact hpb
  · exact hpc
  · exact hA
  · exact hB
  · exact hC

end FrontierNine
#print axioms FrontierNine.nine_trace_ledger
#print axioms FrontierNine.nine_member_ordered_ledger
