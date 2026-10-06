import SunflowerLean.Erdos20V9Profile

namespace Erdos20V10Profile54Score

/-- A member with at most two degree20 points has degree plus singleton
trace at least25 at each point once its meeting family has size at least54.
This declaration is the numerical leaf, without an implicit family proxy. -/
theorem degree_singleton_score_ge_twenty_five
    (sa sb sc sd ta tb tc td a b c d : ℕ)
    (hsa : sa≤10) (hsb : sb≤10) (hsc : sc≤10) (hsd : sd≤10)
    (hta : ta≤1) (htb : tb≤1) (htc : tc≤1) (htd : td≤1)
    (hwa : a+2*sa+ta≤37+(ta+tb+tc+td))
    (hwb : b+2*sb+tb≤37+(ta+tb+tc+td))
    (hwc : c+2*sc+tc≤37+(ta+tb+tc+td))
    (hwd : d+2*sd+td≤37+(ta+tb+tc+td))
    (ha : a≤20) (hb : b≤20) (hc : c≤20) (hd : d≤20)
    (h20a : a=20 → sa=10) (h20b : b=20 → sb=10)
    (h20c : c=20 → sc=10) (h20d : d=20 → sd=10)
    (hnot : ¬ (b=20 ∧ c=20 ∧ d=20))
    (hSum : 110+(ta+tb+tc+td) ≤ a+b+c+d+(sa+sb+sc+sd)) :
    25 ≤ a+sa := by
  have hscore (q s t : ℕ) (hq : q≤20) (hs : s≤10)
      (h20 : q=20 → s=10)
      (hw : q+2*s+t≤37+(ta+tb+tc+td)) (ht : t≤1) :
      q+s≤30 ∧ (q≤19 → q+s≤29) ∧
      (ta+tb+tc+td≤1 → q+s≤28) ∧
      (ta+tb+tc+td=2 → q+s+t≤29) ∧
      (ta+tb+tc+td=3 → q+s+t≤30) := by
    clear * - hq hs h20 hw ht
    have hu : q≤19 ∨ (q=20 ∧ s=10) := by
      by_cases h : q=20
      · exact Or.inr ⟨h,h20 h⟩
      · exact Or.inl (by omega)
    rcases hu with hu | ⟨hu,hu'⟩ <;>
      (repeat' apply And.intro) <;> omega
  obtain ⟨hub,hlb,hub01,hub2,hub3⟩ := hscore b sb tb hb hsb h20b hwb htb
  obtain ⟨huc,hlc,huc01,huc2,huc3⟩ := hscore c sc tc hc hsc h20c hwc htc
  obtain ⟨hud,hld,hud01,hud2,hud3⟩ := hscore d sd td hd hsd h20d hwd htd
  have ht : ta+tb+tc+td≤1 ∨ ta+tb+tc+td=2 ∨
      ta+tb+tc+td=3 ∨ ta+tb+tc+td=4 := by
    clear * - hta htb htc htd
    omega
  rcases ht with ht | ht | ht | ht
  · have ub := hub01 ht
    have uc := huc01 ht
    have ud := hud01 ht
    clear * - ub uc ud hSum
    omega
  · have ub := hub2 ht
    have uc := huc2 ht
    have ud := hud2 ht
    clear * - ub uc ud hSum ht hta
    omega
  · have ub := hub3 ht
    have uc := huc3 ht
    have ud := hud3 ht
    clear * - ub uc ud hSum ht hta
    omega
  · have ho : b+sb+c+sc+d+sd≤89 := by
      clear * - hub huc hud hlb hlc hld hnot hb hc hd
      omega
    clear * - ho ht hSum
    omega

end Erdos20V10Profile54Score
