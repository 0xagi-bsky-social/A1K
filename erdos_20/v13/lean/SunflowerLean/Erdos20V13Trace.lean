import SunflowerLean.Erdos20V12ProfileScoreBridge

namespace Erdos20V12Profile
open Erdos20BCWConditional Erdos20RankThree Erdos20RankFour Erdos20RankFourRefined
open Erdos20SaturatedMeeting Erdos20SharpTriples Erdos20V8Global
open Erdos20V10Profile54Score Erdos20V8ProfileBridge Erdos20V8MeetingProfile Erdos20DegreeCongruences Erdos20V8Boundary

/-- An actual anchor with degree-plus-singleton score at most twenty-five
contains a point of degree twenty. No arithmetic profile is assumed. -/
theorem meeting_fifty_four_low_score_distinct_high_companion
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card=4) (hf : IsSunflowerFree F 3)
    (R : Finset α) (hR : R ∈ F)
    (hc : 54 ≤ (F.filter (fun S => (S ∩ R).Nonempty)).card)
    (x : α) (hx : x ∈ R)
    (hlo : degree F x + (exactTrace F R {x}).card≤25) :
    ∃ y ∈ R, y ≠ x ∧ degree F y=20 := by
  classical
  have herase : (R.erase x).card=3 := by rw [Finset.card_erase_of_mem hx,hu R hR]
  obtain ⟨y,z,w,hyz,hyw,hzw,he⟩ := Finset.card_eq_three.mp herase
  have hnot : x ∉ ({y,z,w} : Finset α) := he ▸ Finset.notMem_erase x R
  have hn : x ≠ y ∧ x ≠ z ∧ x ≠ w := by simpa using hnot
  have hshape : R = {x,y,z,w} := by rw [← he,Finset.insert_erase hx]
  subst R
  let N := F.filter (fun S => (S ∩ {x,y,z,w}).Nonempty)
  have hNF : N ⊆ F := Finset.filter_subset _ _
  have hRN : {x,y,z,w} ∈ N := Finset.mem_filter.mpr ⟨hR,by simp⟩
  have hNu : ∀ S ∈ N, S.card=4 := fun S hS => hu S (hNF hS)
  have hNf : IsSunflowerFree N 3 := fun H hH hs => hf H (hH.trans hNF) hs
  have hhit : ∀ S ∈ N, (S ∩ {x,y,z,w}).Nonempty := fun S hS => (Finset.mem_filter.mp hS).2
  have ht : exactTrace N {x,y,z,w} {x} = exactTrace F {x,y,z,w} {x} := by
    ext S
    simp only [exactTrace,N,Finset.mem_filter]
    constructor
    · rintro ⟨⟨hSF,_⟩,hEq⟩
      exact ⟨hSF,hEq⟩
    · rintro ⟨hSF,hEq⟩
      refine ⟨⟨hSF,?_⟩,hEq⟩
      rw [hEq]
      simp
  have hdeg (p : α) (hp : p ∈ ({x,y,z,w} : Finset α)) : degree N p=degree F p := by
    dsimp only [N]
    exact degree_meeting_restriction_eq F {x,y,z,w} p hp
  have hp := all_meeting_fifty_four_ordered_low_score_high_companion N hNu hNf hc
    x y z w hn.1 hn.2.1 hn.2.2 hyz hyw hzw hRN hhit
    (by rw [ht,hdeg x (by simp)]; exact hlo)
  rw [hdeg y (by simp),hdeg z (by simp),hdeg w (by simp)] at hp
  rcases hp with hp | hp | hp
  · exact ⟨y,by simp,Ne.symm hn.1,hp⟩
  · exact ⟨z,by simp,Ne.symm hn.2.1,hp⟩
  · exact ⟨w,by simp,Ne.symm hn.2.2,hp⟩

end Erdos20V12Profile

namespace Erdos20V13Trace
/-- Exact trace accounting after summing the four point degrees.
The variables are trace-layer totals, not an assumed realizable family. -/
theorem trace_score_identity (s p t m totalDegree : ℕ)
    (hm : m = s + p + t + 1)
    (hd : totalDegree = s + 2*p + 3*t + 4) :
    totalDegree + s = 2*m + 2 + t := by omega

/-- Rewriting the weighted singleton/pair inequality preserves the omitted-point trace. -/
theorem weighted_companion_identity (s p t ti d : ℕ)
    (hd : d + ti = 1 + s + p + t)
    (hw : 3*s + p ≤ 36) : d + 2*s + ti ≤ 37 + t := by omega

/-- A numerical obstruction to replacing 25 by 26 in this relaxation.
This statement constructs no set family. Singleton counts (8,9,9,9),
pair counts all 3, triple counts all 0 and full trace 1 give the displayed data. -/
theorem score_twenty_six_relaxation :
    8+9+9+9+6*3+1 = (54 : ℕ) ∧
    8+3*3+1 = (18 : ℕ) ∧ 9+3*3+1 = (19 : ℕ) ∧
    18+8 = (26 : ℕ) ∧ 19+2*9 ≤ (37 : ℕ) ∧
    3*8+9 ≤ (36 : ℕ) ∧ 3*9+9 ≤ (36 : ℕ) ∧
    110 ≤ (18+8)+(19+9)+(19+9)+(19+9) := by norm_num

/-- Incidence divisibility; the family-level double counting supplies hcount. -/
theorem incidence_divisibility (r k b : ℕ) (hcount : r*k=b) : r ∣ b := ⟨k,hcount.symm⟩

theorem five_cannot_divide_nine (k : ℕ) : 5*k ≠ 9 := by omega
end Erdos20V13Trace

#print axioms Erdos20V12Profile.meeting_fifty_four_low_score_distinct_high_companion
#print axioms Erdos20V13Trace.trace_score_identity
#print axioms Erdos20V13Trace.weighted_companion_identity
#print axioms Erdos20V13Trace.score_twenty_six_relaxation
#print axioms Erdos20V13Trace.incidence_divisibility
#print axioms Erdos20V13Trace.five_cannot_divide_nine
