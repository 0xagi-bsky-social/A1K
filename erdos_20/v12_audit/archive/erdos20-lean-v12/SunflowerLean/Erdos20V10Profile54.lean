import SunflowerLean.Erdos20V9Profile

namespace Erdos20V10Profile54

/-- At meeting size54 and point degrees at most18, all singleton traces
are at least9, and one is saturated at10. This is arithmetic only;
the actual-family interpretation is supplied separately. -/
theorem degree_cap_eighteen_trace_profile54
    (sa sb sc sd ta tb tc td a b c d : ℕ)
    (hsa : sa≤10) (hsb : sb≤10) (hsc : sc≤10) (hsd : sd≤10)
    (hta : ta≤1) (htb : tb≤1) (htc : tc≤1) (htd : td≤1)
    (hwa : a+2*sa+ta≤37+(ta+tb+tc+td))
    (hwb : b+2*sb+tb≤37+(ta+tb+tc+td))
    (hwc : c+2*sc+tc≤37+(ta+tb+tc+td))
    (hwd : d+2*sd+td≤37+(ta+tb+tc+td))
    (ha : a≤18) (hb : b≤18) (hc : c≤18) (hd : d≤18)
    (hSum : 110+(ta+tb+tc+td) ≤ a+b+c+d+(sa+sb+sc+sd)) :
    9≤sa ∧ 9≤sb ∧ 9≤sc ∧ 9≤sd ∧ (sa=10 ∨ sb=10 ∨ sc=10 ∨ sd=10) := by
  have hscore (q s t : ℕ) (hq : q≤18) (hs : s≤10)
      (hw : q+2*s+t≤37+(ta+tb+tc+td)) :
      q+s≤28 ∧ (ta+tb+tc+td=0 → q+s≤27) := by
    clear * - hq hs hw
    omega
  obtain ⟨hua,hza⟩ := hscore a sa ta ha hsa hwa
  obtain ⟨hub,hzb⟩ := hscore b sb tb hb hsb hwb
  obtain ⟨huc,hzc⟩ := hscore c sc tc hc hsc hwc
  obtain ⟨hud,hzd⟩ := hscore d sd td hd hsd hwd
  have htpos : 1≤ta+tb+tc+td := by
    by_contra hn
    have ht : ta+tb+tc+td=0 := by omega
    have hA := hza ht
    have hB := hzb ht
    have hC := hzc ht
    have hD := hzd ht
    clear * - hA hB hC hD ht hSum
    omega
  have hla : 27≤a+sa := by
    clear * - hub huc hud hSum htpos
    omega
  have hlb : 27≤b+sb := by
    clear * - hua huc hud hSum htpos
    omega
  have hlc : 27≤c+sc := by
    clear * - hua hub hud hSum htpos
    omega
  have hld : 27≤d+sd := by
    clear * - hua hub huc hSum htpos
    omega
  refine ⟨?_,?_,?_,?_,?_⟩
  · clear * - hla ha
    omega
  · clear * - hlb hb
    omega
  · clear * - hlc hc
    omega
  · clear * - hld hd
    omega
  · clear * - ha hb hc hd hsa hsb hsc hsd hSum
    omega

end Erdos20V10Profile54
