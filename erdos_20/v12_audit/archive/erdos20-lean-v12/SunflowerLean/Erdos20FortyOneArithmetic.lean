import Mathlib.Tactic

namespace Erdos20FortyOneArithmetic

def LocalDegreePattern (a b c d : ℕ) : Prop :=
  ((a=12 ∨ a=13) ∧ (b=12 ∨ b=13) ∧ (c=12 ∨ c=13) ∧ (d=12 ∨ d=13) ∧
    50 ≤ a+b+c+d ∧ a+b+c+d ≤ 51) ∨
  ((a=14 ∨ a=17) ∧ (b=14 ∨ b=17) ∧ (c=14 ∨ c=17) ∧ (d=14 ∨ d=17) ∧
    62 ≤ a+b+c+d ∧ a+b+c+d ≤ 65) ∨
  ((a=15 ∨ a=16) ∧ (b=15 ∨ b=16) ∧ (c=15 ∨ c=16) ∧ (d=15 ∨ d=16) ∧
    62 ≤ a+b+c+d ∧ a+b+c+d ≤ 63)

/-- Capacity for every opposite pair trace, based on its singleton trace and opposite flag. -/
def capacity (s t : ℕ) : Fin 4 :=
  if 19 ≤ 2*s+3*t then 0 else if 16 ≤ 2*s+3*t then 1 else
    if 13 ≤ 2*s+3*t then 2 else 3

/-- Maximum combined singleton and opposite-triple contribution at each capacity. -/
def ceiling (c : Fin 4) : ℕ :=
  if c = 0 then 10 else if c = 1 then 9 else if c = 2 then 7 else 6

theorem contribution_le_ceiling (s t : ℕ) (hs : s+4*t≤10) (ht : t≤1) :
    s+t ≤ ceiling (capacity s t) := by
  unfold capacity
  split_ifs
  · change s+t ≤ 10; omega
  · change s+t ≤ 9; omega
  · change s+t ≤ 7; omega
  · change s+t ≤ 6; omega

theorem opposite_pair_le_capacity (s t p : ℕ) (hp : p≤3)
    (hw : 2*s+3*p+3*t≤21) : p ≤ (capacity s t).val := by
  unfold capacity
  split_ifs <;> norm_num <;> omega

theorem capacity_one_properties (s t : ℕ) (hs : s+4*t≤10) (ht : t≤1)
    (hc : capacity s t = 1) : t=0 ∧ s≤9 := by
  unfold capacity at hc
  split_ifs at hc <;> norm_num at hc <;> omega

theorem capacity_three_properties (s t : ℕ) (ht : t≤1)
    (hc : capacity s t = 3) : s+2*t≤6 := by
  unfold capacity at hc
  split_ifs at hc <;> norm_num at hc <;> omega

set_option maxRecDepth 4096 in
/-- The complete four-capacity finite certificate; all mixed capacity profiles score at most forty. -/
theorem capacity_profile_certificate : ∀ a b c d : Fin 4,
    41 ≤ ceiling a + ceiling b + ceiling c + ceiling d +
      min a.val b.val + min a.val c.val + min a.val d.val +
      min b.val c.val + min b.val d.val + min c.val d.val →
    (a=1 ∧ b=1 ∧ c=1 ∧ d=1) ∨ (a=3 ∧ b=3 ∧ c=3 ∧ d=3) := by
  decide

/-- Near equality in the all-capacity-one profile gives degrees twelve or thirteen. -/
theorem all_one_pattern
    (a b c d ab ac ad bc bd cd : ℕ)
    (ha : a≤9) (hb : b≤9) (hc : c≤9) (hd : d≤9)
    (hab : ab≤1) (hac : ac≤1) (had : ad≤1) (hbc : bc≤1) (hbd : bd≤1) (hcd : cd≤1)
    (hsum : a+b+c+d+ab+ac+ad+bc+bd+cd=41) :
    LocalDegreePattern (1+a+ab+ac+ad) (1+b+ab+bc+bd)
      (1+c+ac+bc+cd) (1+d+ad+bd+cd) := by
  apply Or.inl
  have ha' : 12 ≤ 1+a+ab+ac+ad ∧ 1+a+ab+ac+ad ≤ 13 := by omega
  have hb' : 12 ≤ 1+b+ab+bc+bd ∧ 1+b+ab+bc+bd ≤ 13 := by omega
  have hc' : 12 ≤ 1+c+ac+bc+cd ∧ 1+c+ac+bc+cd ≤ 13 := by omega
  have hd' : 12 ≤ 1+d+ad+bd+cd ∧ 1+d+ad+bd+cd ≤ 13 := by omega
  refine ⟨by omega,by omega,by omega,by omega,?_,?_⟩ <;> omega

/-- Near equality with capacity three and no triple trace gives degrees fifteen or sixteen. -/
theorem all_three_zero_pattern
    (a b c d ab ac ad bc bd cd : ℕ)
    (ha : a≤6) (hb : b≤6) (hc : c≤6) (hd : d≤6)
    (hab : ab≤3) (hac : ac≤3) (had : ad≤3) (hbc : bc≤3) (hbd : bd≤3) (hcd : cd≤3)
    (hsum : a+b+c+d+ab+ac+ad+bc+bd+cd=41) :
    LocalDegreePattern (1+a+ab+ac+ad) (1+b+ab+bc+bd)
      (1+c+ac+bc+cd) (1+d+ad+bd+cd) := by
  apply Or.inr
  apply Or.inr
  have ha' : 15 ≤ 1+a+ab+ac+ad ∧ 1+a+ab+ac+ad ≤ 16 := by omega
  have hb' : 15 ≤ 1+b+ab+bc+bd ∧ 1+b+ab+bc+bd ≤ 16 := by omega
  have hc' : 15 ≤ 1+c+ac+bc+cd ∧ 1+c+ac+bc+cd ≤ 16 := by omega
  have hd' : 15 ≤ 1+d+ad+bd+cd ∧ 1+d+ad+bd+cd ≤ 16 := by omega
  refine ⟨by omega,by omega,by omega,by omega,?_,?_⟩ <;> omega

/-- At capacity three, exactly one triple trace forces degree fourteen at its opposite point. -/
theorem all_three_one_pattern
    (a b c d ab ac ad bc bd cd ta tb tc td : ℕ)
    (ha : a+2*ta≤6) (hb : b+2*tb≤6) (hc : c+2*tc≤6) (hd : d+2*td≤6)
    (hab : ab≤3) (hac : ac≤3) (had : ad≤3) (hbc : bc≤3) (hbd : bd≤3) (hcd : cd≤3)
    (ht : ta+tb+tc+td=1)
    (hsum : a+b+c+d+ab+ac+ad+bc+bd+cd+ta+tb+tc+td=41) :
    LocalDegreePattern
      (1+a+ab+ac+ad+tb+tc+td) (1+b+ab+bc+bd+ta+tc+td)
      (1+c+ac+bc+cd+ta+tb+td) (1+d+ad+bd+cd+ta+tb+tc) := by
  apply Or.inr
  apply Or.inl
  have hP : ab=3 ∧ ac=3 ∧ ad=3 ∧ bc=3 ∧ bd=3 ∧ cd=3 := by omega
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := hP
  have hs : a+2*ta=6 ∧ b+2*tb=6 ∧ c+2*tc=6 ∧ d+2*td=6 := by omega
  have ha' : 1+a+3+3+3+tb+tc+td=14 ∨ 1+a+3+3+3+tb+tc+td=17 := by
    rcases (show ta=0 ∨ ta=1 by omega) with he | he <;> omega
  have hb' : 1+b+3+3+3+ta+tc+td=14 ∨ 1+b+3+3+3+ta+tc+td=17 := by
    rcases (show tb=0 ∨ tb=1 by omega) with he | he <;> omega
  have hc' : 1+c+3+3+3+ta+tb+td=14 ∨ 1+c+3+3+3+ta+tb+td=17 := by
    rcases (show tc=0 ∨ tc=1 by omega) with he | he <;> omega
  have hd' : 1+d+3+3+3+ta+tb+tc=14 ∨ 1+d+3+3+3+ta+tb+tc=17 := by
    rcases (show td=0 ∨ td=1 by omega) with he | he <;> omega
  exact ⟨ha',hb',hc',hd',by omega,by omega⟩

/-- Reassociation of the fourteen trace contributions. -/
theorem grouped_contribution_sum
    (a b c d ab ac ad bc bd cd ta tb tc td : ℕ)
    (hsum : a+b+c+d+ab+ac+ad+bc+bd+cd+ta+tb+tc+td=41) :
    (a+ta)+(b+tb)+(c+tc)+(d+td)+ab+ac+ad+bc+bd+cd=41 := by omega

/-- The capacity-three inequalities leave room for at most one triple trace. -/
theorem all_three_triple_sum_le_one
    (a b c d ab ac ad bc bd cd ta tb tc td : ℕ)
    (ha : a+2*ta≤6) (hb : b+2*tb≤6) (hc : c+2*tc≤6) (hd : d+2*td≤6)
    (hab : ab≤3) (hac : ac≤3) (had : ad≤3) (hbc : bc≤3) (hbd : bd≤3) (hcd : cd≤3)
    (hsum : a+b+c+d+ab+ac+ad+bc+bd+cd+ta+tb+tc+td=41) :
    ta+tb+tc+td≤1 := by omega

/-- A zero sum of four natural-number flags sets every flag to zero. -/
theorem four_flags_sum_zero (a b c d : ℕ) (h : a+b+c+d=0) :
    a=0 ∧ b=0 ∧ c=0 ∧ d=0 := by omega

/-- Exact degree patterns at forty-two members, via a bounded four-capacity certificate. -/
theorem local_pattern
    (a b c d ab ac ad bc bd cd ta tb tc td : ℕ)
    (ha : a+4*ta ≤ 10) (hb : b+4*tb ≤ 10) (hc : c+4*tc ≤ 10) (hd : d+4*td ≤ 10)
    (hab : ab≤3) (hac : ac≤3) (had : ad≤3) (hbc : bc≤3) (hbd : bd≤3) (hcd : cd≤3)
    (hta : ta≤1) (htb : tb≤1) (htc : tc≤1) (htd : td≤1)
    (h1 : 2*a+3*bc+3*ta≤21) (h2 : 2*a+3*bd+3*ta≤21) (h3 : 2*a+3*cd+3*ta≤21)
    (h4 : 2*b+3*ac+3*tb≤21) (h5 : 2*b+3*ad+3*tb≤21) (h6 : 2*b+3*cd+3*tb≤21)
    (h7 : 2*c+3*ab+3*tc≤21) (h8 : 2*c+3*ad+3*tc≤21) (h9 : 2*c+3*bd+3*tc≤21)
    (h10 : 2*d+3*ab+3*td≤21) (h11 : 2*d+3*ac+3*td≤21) (h12 : 2*d+3*bc+3*td≤21)
    (hsum : a+b+c+d+ab+ac+ad+bc+bd+cd+ta+tb+tc+td=41) :
    LocalDegreePattern
      (1+a+ab+ac+ad+tb+tc+td) (1+b+ab+bc+bd+ta+tc+td)
      (1+c+ac+bc+cd+ta+tb+td) (1+d+ad+bd+cd+ta+tb+tc) := by
  let A := capacity a ta
  let B := capacity b tb
  let C := capacity c tc
  let D := capacity d td
  have hA : a+ta ≤ ceiling A := contribution_le_ceiling a ta ha hta
  have hB : b+tb ≤ ceiling B := contribution_le_ceiling b tb hb htb
  have hC : c+tc ≤ ceiling C := contribution_le_ceiling c tc hc htc
  have hD : d+td ≤ ceiling D := contribution_le_ceiling d td hd htd
  have hab' : ab ≤ min C.val D.val := le_min
    (opposite_pair_le_capacity c tc ab hab h7) (opposite_pair_le_capacity d td ab hab h10)
  have hac' : ac ≤ min B.val D.val := le_min
    (opposite_pair_le_capacity b tb ac hac h4) (opposite_pair_le_capacity d td ac hac h11)
  have had' : ad ≤ min B.val C.val := le_min
    (opposite_pair_le_capacity b tb ad had h5) (opposite_pair_le_capacity c tc ad had h8)
  have hbc' : bc ≤ min A.val D.val := le_min
    (opposite_pair_le_capacity a ta bc hbc h1) (opposite_pair_le_capacity d td bc hbc h12)
  have hbd' : bd ≤ min A.val C.val := le_min
    (opposite_pair_le_capacity a ta bd hbd h2) (opposite_pair_le_capacity c tc bd hbd h9)
  have hcd' : cd ≤ min A.val B.val := le_min
    (opposite_pair_le_capacity a ta cd hcd h3) (opposite_pair_le_capacity b tb cd hcd h6)
  have hscore : 41 ≤ ceiling A + ceiling B + ceiling C + ceiling D +
      min A.val B.val + min A.val C.val + min A.val D.val +
      min B.val C.val + min B.val D.val + min C.val D.val := by
    calc
      41 = (a+ta)+(b+tb)+(c+tc)+(d+td)+ab+ac+ad+bc+bd+cd :=
        (grouped_contribution_sum a b c d ab ac ad bc bd cd ta tb tc td hsum).symm
      _ ≤ ceiling A + ceiling B + ceiling C + ceiling D +
          min C.val D.val + min B.val D.val + min B.val C.val +
          min A.val D.val + min A.val C.val + min A.val B.val :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
            (Nat.add_le_add hA hB) hC) hD) hab') hac') had') hbc') hbd') hcd'
      _ = _ := by ac_rfl
  rcases capacity_profile_certificate A B C D hscore with
    ⟨hAeq,hBeq,hCeq,hDeq⟩ | ⟨hAeq,hBeq,hCeq,hDeq⟩
  · obtain ⟨hta0,ha9⟩ := capacity_one_properties a ta ha hta hAeq
    obtain ⟨htb0,hb9⟩ := capacity_one_properties b tb hb htb hBeq
    obtain ⟨htc0,hc9⟩ := capacity_one_properties c tc hc htc hCeq
    obtain ⟨htd0,hd9⟩ := capacity_one_properties d td hd htd hDeq
    have hab1 : ab≤1 := by simpa [hCeq,hDeq] using hab'
    have hac1 : ac≤1 := by simpa [hBeq,hDeq] using hac'
    have had1 : ad≤1 := by simpa [hBeq,hCeq] using had'
    have hbc1 : bc≤1 := by simpa [hAeq,hDeq] using hbc'
    have hbd1 : bd≤1 := by simpa [hAeq,hCeq] using hbd'
    have hcd1 : cd≤1 := by simpa [hAeq,hBeq] using hcd'
    subst ta; subst tb; subst tc; subst td
    simpa only [Nat.add_zero] using all_one_pattern a b c d ab ac ad bc bd cd
      ha9 hb9 hc9 hd9 hab1 hac1 had1 hbc1 hbd1 hcd1 (by simpa only [Nat.add_zero] using hsum)
  · have ha6 := capacity_three_properties a ta hta hAeq
    have hb6 := capacity_three_properties b tb htb hBeq
    have hc6 := capacity_three_properties c tc htc hCeq
    have hd6 := capacity_three_properties d td htd hDeq
    have hT : ta+tb+tc+td ≤ 1 := all_three_triple_sum_le_one
      a b c d ab ac ad bc bd cd ta tb tc td ha6 hb6 hc6 hd6 hab hac had hbc hbd hcd hsum
    by_cases hz : ta+tb+tc+td=0
    · obtain ⟨hta0,htb0,htc0,htd0⟩ := four_flags_sum_zero ta tb tc td hz
      subst ta; subst tb; subst tc; subst td
      simpa only [Nat.add_zero] using all_three_zero_pattern a b c d ab ac ad bc bd cd
        (by simpa using ha6) (by simpa using hb6) (by simpa using hc6) (by simpa using hd6)
        hab hac had hbc hbd hcd (by simpa only [Nat.add_zero] using hsum)
    · exact all_three_one_pattern a b c d ab ac ad bc bd cd ta tb tc td
        ha6 hb6 hc6 hd6 hab hac had hbc hbd hcd (Nat.le_antisymm hT (Nat.pos_of_ne_zero hz)) hsum

end Erdos20FortyOneArithmetic
