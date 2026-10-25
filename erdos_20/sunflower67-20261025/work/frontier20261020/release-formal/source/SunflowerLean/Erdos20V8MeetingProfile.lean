import Mathlib.Tactic

/-! Arithmetic consequences of an actual meeting neighborhood of cardinality56.
The finite-set bridge and global equality obstruction are separate obligations. -/
namespace Erdos20V8MeetingProfile

/-- Every point has degree18–20; degree18 forces the other three degrees20;
at least one and at most three points have degree20. -/
def DegreePattern (a b c d : ℕ) : Prop :=
  (18≤a ∧ a≤20) ∧ (18≤b ∧ b≤20) ∧ (18≤c ∧ c≤20) ∧ (18≤d ∧ d≤20) ∧
  (a=20 ∨ b=20 ∨ c=20 ∨ d=20) ∧ ¬(a=20 ∧ b=20 ∧ c=20 ∧ d=20) ∧
  (a=18 → b=20 ∧ c=20 ∧ d=20) ∧ (b=18 → a=20 ∧ c=20 ∧ d=20) ∧
  (c=18 → a=20 ∧ b=20 ∧ d=20) ∧ (d=18 → a=20 ∧ b=20 ∧ c=20)

set_option maxHeartbeats 800000 in
/-- Exact arithmetic restriction on the four anchor degrees at meeting cardinality56. -/
theorem meeting_fifty_six_degree_pattern
    (sa sb sc sd ab ac ad bc bd cd ta tb tc td a b c d : ℕ)
    (hsa : sa≤10) (hsb : sb≤10) (hsc : sc≤10) (hsd : sd≤10)
    (_hab : ab≤3) (_hac : ac≤3) (_had : ad≤3) (_hbc : bc≤3) (_hbd : bd≤3) (_hcd : cd≤3)
    (hta : ta≤1) (htb : tb≤1) (htc : tc≤1) (htd : td≤1)
    (hwa : 3*sa+ab+ac+ad≤36) (hwb : 3*sb+ab+bc+bd≤36)
    (hwc : 3*sc+ac+bc+cd≤36) (hwd : 3*sd+ad+bd+cd≤36)
    (hea : a=1+sa+ab+ac+ad+tb+tc+td)
    (heb : b=1+sb+ab+bc+bd+ta+tc+td)
    (hec : c=1+sc+ac+bc+cd+ta+tb+td)
    (hed : d=1+sd+ad+bd+cd+ta+tb+tc)
    (ha : a≤20) (hb : b≤20) (hc : c≤20) (hd : d≤20)
    (h20a : a=20 → sa=10) (h20b : b=20 → sb=10)
    (h20c : c=20 → sc=10) (h20d : d=20 → sd=10)
    (hn : sa+sb+sc+sd+ab+ac+ad+bc+bd+cd+ta+tb+tc+td=55) :
    DegreePattern a b c d := by
  have hW : 3*(sa+sb+sc+sd)+2*(ab+ac+ad+bc+bd+cd)≤144 := by
    clear * - hwa hwb hwc hwd
    omega
  have hSum : a+b+c+d+(sa+sb+sc+sd)=114+(ta+tb+tc+td) := by
    clear * - hea heb hec hed hn
    omega
  have hS : sa+sb+sc+sd≤40 := by
    clear * - hsa hsb hsc hsd
    omega
  have hI : 77≤a+b+c+d := by
    clear * - hW hSum hn hS
    omega
  have hA : a≤19 ∨ (a=20 ∧ sa=10 ∧ tb=1 ∧ tc=1 ∧ td=1) := by
    by_cases h : a=20
    · have hs := h20a h
      right
      clear * - h hs hea hwa htb htc htd
      omega
    · left
      clear * - ha h
      omega
  have hB : b≤19 ∨ (b=20 ∧ sb=10 ∧ ta=1 ∧ tc=1 ∧ td=1) := by
    by_cases h : b=20
    · have hs := h20b h
      right
      clear * - h hs heb hwb hta htc htd
      omega
    · left
      clear * - hb h
      omega
  have hC : c≤19 ∨ (c=20 ∧ sc=10 ∧ ta=1 ∧ tb=1 ∧ td=1) := by
    by_cases h : c=20
    · have hs := h20c h
      right
      clear * - h hs hec hwc hta htb htd
      omega
    · left
      clear * - hc h
      omega
  have hD : d≤19 ∨ (d=20 ∧ sd=10 ∧ ta=1 ∧ tb=1 ∧ tc=1) := by
    by_cases h : d=20
    · have hs := h20d h
      right
      clear * - h hs hed hwd hta htb htc
      omega
    · left
      clear * - hd h
      omega
  clear * - hSum hS hI hA hB hC hD ha hb hc hd
  rcases hA with hA | ⟨hA,hsA,htAB,htAC,htAD⟩ <;>
    rcases hB with hB | ⟨hB,hsB,htBA,htBC,htBD⟩ <;>
    rcases hC with hC | ⟨hC,hsC,htCA,htCB,htCD⟩ <;>
    rcases hD with hD | ⟨hD,hsD,htDA,htDB,htDC⟩
  all_goals unfold DegreePattern; omega

/-- The proposed final weighted-count obstruction has no nonnegative integer solution. -/
theorem no_weighted_eighty_three_equality (A B C : ℕ) : 12 ≠ 18*A+14*B+7*C := by omega

/-- Equivalent form of the weighted obstruction when nine high-degree points are classified. -/
theorem no_nine_high_point_weighted_equality (A B C D : ℕ)
    (hn : A+B+C+D=9) : 6*83 ≠ 72*A+68*B+61*C+54*D := by omega


/-- Nine point weights from the four design possibilities cannot sum to six times83. -/
theorem no_nine_point_weight_sum
    {α : Type*} [DecidableEq α] (T : Finset α) (f : α → ℕ)
    (hc : T.card = 9) (hv : ∀ x ∈ T, f x=54 ∨ f x=61 ∨ f x=68 ∨ f x=72)
    (hs : (∑ x ∈ T, f x) = 498) : False := by
  classical
  have repr (U : Finset α) (hU : ∀ x ∈ U, f x=54 ∨ f x=61 ∨ f x=68 ∨ f x=72) :
      ∃ A B C D : ℕ, A+B+C+D=U.card ∧
        (∑ x ∈ U, f x)=72*A+68*B+61*C+54*D := by
    induction U using Finset.induction_on with
    | empty => exact ⟨0,0,0,0,by simp⟩
    | @insert x U hx ih =>
      obtain ⟨A,B,C,D,hn,he⟩ := ih (fun y hy => hU y (Finset.mem_insert_of_mem hy))
      have hh := hU x (Finset.mem_insert_self x U)
      rw [Finset.card_insert_of_notMem hx,Finset.sum_insert hx,he]
      rcases hh with hh | hh | hh | hh
      · exact ⟨A,B,C,D+1,by omega⟩
      · exact ⟨A,B,C+1,D,by omega⟩
      · exact ⟨A,B+1,C,D,by omega⟩
      · exact ⟨A+1,B,C,D,by omega⟩
  obtain ⟨A,B,C,D,hn,he⟩ := repr T hv
  apply no_nine_high_point_weighted_equality A B C D (hn.trans hc)
  omega

end Erdos20V8MeetingProfile
