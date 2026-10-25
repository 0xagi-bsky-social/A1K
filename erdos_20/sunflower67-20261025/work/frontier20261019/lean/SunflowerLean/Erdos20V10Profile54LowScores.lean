import SunflowerLean.Erdos20V9Profile

namespace Erdos20V10Profile54LowScores

/-- Two degree-plus-singleton scores cannot both be at most26 in the
meeting54 trace system. Family semantics are supplied in a separate bridge. -/
theorem not_two_degree_singleton_scores_le_twenty_six
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
    (hloA : a+sa≤26) (hloB : b+sb≤26)
    (hSum : 110+(ta+tb+tc+td) ≤ a+b+c+d+(sa+sb+sc+sd)) :
    False := by
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
  obtain ⟨huc,hlc,huc01,huc2,huc3⟩ := hscore c sc tc hc hsc h20c hwc htc
  obtain ⟨hud,hld,hud01,hud2,hud3⟩ := hscore d sd td hd hsd h20d hwd htd
  have ht : ta+tb+tc+td≤1 ∨ ta+tb+tc+td=2 ∨ 3≤ta+tb+tc+td := by omega
  rcases ht with ht | ht | ht
  · have uc := huc01 ht
    have ud := hud01 ht
    clear * - uc ud hSum hloA hloB
    omega
  · have uc := huc2 ht
    have ud := hud2 ht
    clear * - uc ud hSum ht hta htb hloA hloB
    omega
  · clear * - huc hud ht hSum hloA hloB
    omega

end Erdos20V10Profile54LowScores
