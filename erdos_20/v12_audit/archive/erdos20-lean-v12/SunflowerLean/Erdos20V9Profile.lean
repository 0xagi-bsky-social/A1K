import SunflowerLean.Erdos20V8MeetingProfile

namespace Erdos20V9Profile

/-- The near-boundary degree restrictions before using global pair incidences. -/
def DegreePattern55 (a b c d : ℕ) : Prop :=
  (16 ≤ a ∧ a ≤ 20) ∧ (16 ≤ b ∧ b ≤ 20) ∧
  (16 ≤ c ∧ c ≤ 20) ∧ (16 ≤ d ∧ d ≤ 20) ∧
  ¬ (a=20 ∧ b=20 ∧ c=20 ∧ d=20) ∧
  (a=16 → b=20 ∧ c=20 ∧ d=20) ∧
  (b=16 → a=20 ∧ c=20 ∧ d=20) ∧
  (c=16 → a=20 ∧ b=20 ∧ d=20) ∧
  (d=16 → a=20 ∧ b=20 ∧ c=20) ∧
  (a=17 → 19≤b ∧ 19≤c ∧ 19≤d ∧ (b=20 ∨ c=20 ∨ d=20)) ∧
  (b=17 → 19≤a ∧ 19≤c ∧ 19≤d ∧ (a=20 ∨ c=20 ∨ d=20)) ∧
  (c=17 → 19≤a ∧ 19≤b ∧ 19≤d ∧ (a=20 ∨ b=20 ∨ d=20)) ∧
  (d=17 → 19≤a ∧ 19≤b ∧ 19≤c ∧ (a=20 ∨ b=20 ∨ c=20)) ∧
  ¬(a≤18 ∧ b≤18 ∧ c≤18) ∧ ¬(a≤18 ∧ b≤18 ∧ d≤18) ∧
  ¬(a≤18 ∧ c≤18 ∧ d≤18) ∧ ¬(b≤18 ∧ c≤18 ∧ d≤18)

set_option maxHeartbeats 400000 in
/-- Meeting55 profile from aggregate trace identities and weighted point incidences. -/
theorem degree_pattern55_of_moments
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
    (hSum : a+b+c+d+(sa+sb+sc+sd)=112+(ta+tb+tc+td))
    (hW : sa+sb+sc+sd≤36+2*(ta+tb+tc+td)) :
    DegreePattern55 a b c d := by
  have hscore (q s t : ℕ) (hq : q≤20) (hs : s≤10)
      (h20 : q=20 → s=10)
      (hw : q+2*s+t≤37+(ta+tb+tc+td)) (ht : t≤1) :
      q+s≤30 ∧ (q≤19 → q+s≤29) ∧ (q≤18 → q+s≤28) ∧
      (ta+tb+tc+td≤1 → q+s≤28) ∧
      (ta+tb+tc+td=2 → q+s+t≤29 ∧ q≤19) ∧
      (ta+tb+tc+td=3 → q+s+t≤30 ∧ (t=1 → q≤19)) := by
    clear * - hq hs h20 hw ht
    have hu : q≤19 ∨ (q=20 ∧ s=10) := by
      by_cases h : q=20
      · exact Or.inr ⟨h,h20 h⟩
      · exact Or.inl (by omega)
    rcases hu with hu | ⟨hu,hu'⟩ <;>
      (repeat' apply And.intro) <;> omega
  obtain ⟨hua,hla,hla18,hua01,hua2,hua3⟩ := hscore a sa ta ha hsa h20a hwa hta
  obtain ⟨hub,hlb,hlb18,hub01,hub2,hub3⟩ := hscore b sb tb hb hsb h20b hwb htb
  obtain ⟨huc,hlc,hlc18,huc01,huc2,huc3⟩ := hscore c sc tc hc hsc h20c hwc htc
  obtain ⟨hud,hld,hld18,hud01,hud2,hud3⟩ := hscore d sd td hd hsd h20d hwd htd
  have ht : ta+tb+tc+td=0 ∨ ta+tb+tc+td=1 ∨ ta+tb+tc+td=2 ∨
      ta+tb+tc+td=3 ∨ ta+tb+tc+td=4 := by
    clear * - hta htb htc htd
    omega
  rcases ht with ht | ht | ht | ht | ht
  · have ua := hua01 (by clear * - ht; omega)
    have ub := hub01 (by clear * - ht; omega)
    have uc := huc01 (by clear * - ht; omega)
    have ud := hud01 (by clear * - ht; omega)
    have hvals : a=19 ∧ b=19 ∧ c=19 ∧ d=19 := by
      clear * - ua ub uc ud ht hSum hwa hwb hwc hwd ha hb hc hd h20a h20b h20c h20d
      omega
    rcases hvals with ⟨rfl,rfl,rfl,rfl⟩
    simp [DegreePattern55]
  · have ua := hua01 (by clear * - ht; omega)
    have ub := hub01 (by clear * - ht; omega)
    have uc := huc01 (by clear * - ht; omega)
    have ud := hud01 (by clear * - ht; omega)
    clear * - ua ub uc ud ht hSum
    omega
  · obtain ⟨ua,ha19⟩ := hua2 ht
    obtain ⟨ub,hb19⟩ := hub2 ht
    obtain ⟨uc,hc19⟩ := huc2 ht
    obtain ⟨ud,hd19⟩ := hud2 ht
    have hva : a+sa+ta=29 ∧ b+sb+tb=29 ∧ c+sc+tc=29 ∧ d+sd+td=29 := by
      clear * - ua ub uc ud ht hSum
      omega
    clear * - hva ht hsa hsb hsc hsd hta htb htc htd ha19 hb19 hc19 hd19
    unfold DegreePattern55
    repeat' apply And.intro
    all_goals omega
  · obtain ⟨ua,ha19⟩ := hua3 ht
    obtain ⟨ub,hb19⟩ := hub3 ht
    obtain ⟨uc,hc19⟩ := huc3 ht
    obtain ⟨ud,hd19⟩ := hud3 ht
    have hn20 : ¬(a=20 ∧ b=20 ∧ c=20 ∧ d=20) := by
      clear * - ha19 hb19 hc19 hd19 ht hta htb htc htd
      omega
    clear * - ua ub uc ud ht hSum hsa hsb hsc hsd hta htb htc htd ha hb hc hd hn20
    unfold DegreePattern55
    repeat' apply And.intro
    all_goals omega
  · have hn20 : ¬(a=20 ∧ b=20 ∧ c=20 ∧ d=20) := by
      rintro ⟨heA,heB,heC,heD⟩
      have seA := h20a heA
      have seB := h20b heB
      have seC := h20c heC
      have seD := h20d heD
      clear * - heA heB heC heD seA seB seC seD ht hSum
      omega
    clear * - hua hub huc hud hsa hsb hsc hsd ha hb hc hd ht hSum hn20
    unfold DegreePattern55
    repeat' apply And.intro
    all_goals omega

end Erdos20V9Profile
