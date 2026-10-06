import SunflowerLean.Erdos20V10Profile54Score

namespace Erdos20V12Profile

/-- A degree-plus-singleton score at most twenty-five forces another
point to have degree twenty in a meeting-at-least-fifty-four anchor. -/
theorem score_twenty_five_forces_degree_twenty
    (sa sb sc sd ta tb tc td a b c d : ℕ)
    (hsb : sb≤10) (hsc : sc≤10) (hsd : sd≤10)
    (hta : ta≤1) (htb : tb≤1) (htc : tc≤1) (htd : td≤1)
    (hwb : b+2*sb+tb≤37+(ta+tb+tc+td))
    (hwc : c+2*sc+tc≤37+(ta+tb+tc+td))
    (hwd : d+2*sd+td≤37+(ta+tb+tc+td))
    (hb : b≤20) (hc : c≤20) (hd : d≤20)
    (hlow : a+sa≤25)
    (hSum : 110+(ta+tb+tc+td) ≤ a+b+c+d+(sa+sb+sc+sd)) :
    b=20 ∨ c=20 ∨ d=20 := by
  by_contra hn
  have hb19 : b≤19 := by omega
  have hc19 : c≤19 := by omega
  have hd19 : d≤19 := by omega
  have ub : b+sb≤29 := by omega
  have uc : c+sc≤29 := by omega
  have ud : d+sd≤29 := by omega
  have ht : ta+tb+tc+td≤1 ∨ ta+tb+tc+td=2 ∨ 3≤ta+tb+tc+td := by omega
  rcases ht with ht | ht | ht
  · have ub' : b+sb≤28 := by omega
    have uc' : c+sc≤28 := by omega
    have ud' : d+sd≤28 := by omega
    omega
  · have ub' : b+sb+tb≤29 := by omega
    have uc' : c+sc+tc≤29 := by omega
    have ud' : d+sd+td≤29 := by omega
    omega
  · omega

end Erdos20V12Profile
