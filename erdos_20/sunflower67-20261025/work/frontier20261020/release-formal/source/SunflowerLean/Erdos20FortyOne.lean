import SunflowerLean.Erdos20FortyOneArithmetic
import SunflowerLean.Erdos20RankFourRefined
import SunflowerLean.Erdos20DegreeCongruences

namespace Erdos20FortyOne
open Erdos20BCWConditional Erdos20RankThree Erdos20RankFour Erdos20RankFourRefined
open Erdos20FortyOneArithmetic Erdos20SharpTriples

set_option maxHeartbeats 600000 in
theorem forty_two_ordered_degree_pattern
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 42)
    (x y z w : α) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) (hR : {x,y,z,w} ∈ F) :
    LocalDegreePattern ((F.filter (fun S => x ∈ S)).card)
      ((F.filter (fun S => y ∈ S)).card) ((F.filter (fun S => z ∈ S)).card)
      ((F.filter (fun S => w ∈ S)).card) := by
  classical
  let n : Finset α → ℕ := fun C => (exactTrace F {x,y,z,w} C).card
  have hpart := card_eq_sum_exact_traces F {x,y,z,w}
  change F.card = ∑ C ∈ ({x,y,z,w} : Finset α).powerset, n C at hpart
  rw [sum_powerset_four n x y z w hxy hxz hxw hyz hyw hzw] at hpart
  have h0 : n ∅ = 0 := empty_trace_card_eq_zero F {x,y,z,w} hR hi
  have h4 : n {x,y,z,w} = 1 := full_trace_card_eq_one F {x,y,z,w} 4 hR hu
  have hp (a : α) (C D : Finset α) (hC : C.card = 2) (haC : a ∉ C)
      (hD : D.card = 3) (hDR : D ⊆ ({x,y,z,w} : Finset α)) (haD : a ∉ D) :
      2 * n {a} + 3 * n C + 3 * n D ≤ 21 :=
    singleton_pair_triple_trace_weighted_le_twenty_one F {x,y,z,w} C D a
      hR hu hf hi hC haC hDR hD haD
  have hp1 := hp x {y,z} {y,z,w} (by simp [hyz]) (by simp [hxy,hxz]) (by simp [hyz,hyw,hzw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [hxy,hxz,hxw])
  have hp2 := hp x {y,w} {y,z,w} (by simp [hyw]) (by simp [hxy,hxw]) (by simp [hyz,hyw,hzw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [hxy,hxz,hxw])
  have hp3 := hp x {z,w} {y,z,w} (by simp [hzw]) (by simp [hxz,hxw]) (by simp [hyz,hyw,hzw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [hxy,hxz,hxw])
  have hp4 := hp y {x,z} {x,z,w} (by simp [hxz]) (by simp [Ne.symm hxy,hyz]) (by simp [hxz,hxw,hzw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxy,hyz,hyw])
  have hp5 := hp y {x,w} {x,z,w} (by simp [hxw]) (by simp [Ne.symm hxy,hyw]) (by simp [hxz,hxw,hzw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxy,hyz,hyw])
  have hp6 := hp y {z,w} {x,z,w} (by simp [hzw]) (by simp [hyz,hyw]) (by simp [hxz,hxw,hzw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxy,hyz,hyw])
  have hp7 := hp z {x,y} {x,y,w} (by simp [hxy]) (by simp [Ne.symm hxz,Ne.symm hyz]) (by simp [hxy,hxw,hyw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxz,Ne.symm hyz,hzw])
  have hp8 := hp z {x,w} {x,y,w} (by simp [hxw]) (by simp [Ne.symm hxz,hzw]) (by simp [hxy,hxw,hyw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxz,Ne.symm hyz,hzw])
  have hp9 := hp z {y,w} {x,y,w} (by simp [hyw]) (by simp [Ne.symm hyz,hzw]) (by simp [hxy,hxw,hyw]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxz,Ne.symm hyz,hzw])
  have hp10 := hp w {x,y} {x,y,z} (by simp [hxy]) (by simp [Ne.symm hxw,Ne.symm hyw]) (by simp [hxy,hxz,hyz]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxw,Ne.symm hyw,Ne.symm hzw])
  have hp11 := hp w {x,z} {x,y,z} (by simp [hxz]) (by simp [Ne.symm hxw,Ne.symm hzw]) (by simp [hxy,hxz,hyz]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxw,Ne.symm hyw,Ne.symm hzw])
  have hp12 := hp w {y,z} {x,y,z} (by simp [hyz]) (by simp [Ne.symm hyw,Ne.symm hzw]) (by simp [hxy,hxz,hyz]) (by intro q hq; simp only [Finset.mem_insert,Finset.mem_singleton] at hq ⊢; rcases hq with rfl | rfl | rfl <;> simp) (by simp [Ne.symm hxw,Ne.symm hyw,Ne.symm hzw])
  have ht (a : α) (C : Finset α) (hC : C.card = 3)
      (hCR : C ⊆ ({x,y,z,w} : Finset α)) (haC : a ∉ C) :
      n {a} + 4 * n C ≤ 10 :=
    singleton_triple_trace_weighted_le_ten F {x,y,z,w} C a hR hu hf hi hCR hC haC
  have ht1 := ht x {y,z,w} (by simp [hyz,hyw,hzw]) (by simp) (by simp [hxy,hxz,hxw])
  have ht2 := ht y {x,z,w} (by simp [hxz,hxw,hzw]) (by simp [Finset.insert_subset_iff]) (by simp [Ne.symm hxy,hyz,hyw])
  have ht3 := ht z {x,y,w} (by simp [hxy,hxw,hyw]) (by simp [Finset.insert_subset_iff]) (by simp [Ne.symm hxz,Ne.symm hyz,hzw])
  have ht4 := ht w {x,y,z} (by simp [hxy,hxz,hyz]) (by simp [Finset.insert_subset_iff]) (by simp [Ne.symm hxw,Ne.symm hyw,Ne.symm hzw])
  have hb1 : n {x,y} ≤ 3 := pair_trace_card_le_three F {x,y,z,w} {x,y} hR hu hf (by simp [hxy])
  have hb2 : n {x,z} ≤ 3 := pair_trace_card_le_three F {x,y,z,w} {x,z} hR hu hf (by simp [hxz])
  have hb3 : n {x,w} ≤ 3 := pair_trace_card_le_three F {x,y,z,w} {x,w} hR hu hf (by simp [hxw])
  have hb4 : n {y,z} ≤ 3 := pair_trace_card_le_three F {x,y,z,w} {y,z} hR hu hf (by simp [hyz])
  have hb5 : n {y,w} ≤ 3 := pair_trace_card_le_three F {x,y,z,w} {y,w} hR hu hf (by simp [hyw])
  have hb6 : n {z,w} ≤ 3 := pair_trace_card_le_three F {x,y,z,w} {z,w} hR hu hf (by simp [hzw])
  have hc1 : n {y,z,w} ≤ 1 := triple_trace_card_le_one F {x,y,z,w} {y,z,w} hR hu hf (by simp) (by simp [hyz,hyw,hzw])
  have hc2 : n {x,z,w} ≤ 1 := triple_trace_card_le_one F {x,y,z,w} {x,z,w} hR hu hf (by simp [Finset.insert_subset_iff]) (by simp [hxz,hxw,hzw])
  have hc3 : n {x,y,w} ≤ 1 := triple_trace_card_le_one F {x,y,z,w} {x,y,w} hR hu hf (by simp [Finset.insert_subset_iff]) (by simp [hxy,hxw,hyw])
  have hc4 : n {x,y,z} ≤ 1 := triple_trace_card_le_one F {x,y,z,w} {x,y,z} hR hu hf (by simp [Finset.insert_subset_iff]) (by simp [hxy,hxz,hyz])
  have hsumN : n {x}+n {y}+n {z}+n {w}+n {x,y}+n {x,z}+n {x,w}+
      n {y,z}+n {y,w}+n {z,w}+n {y,z,w}+n {x,z,w}+n {x,y,w}+n {x,y,z}=41 := by
    clear * - hpart h0 h4 hc
    omega
  have hpat := local_pattern (n {x}) (n {y}) (n {z}) (n {w})
    (n {x,y}) (n {x,z}) (n {x,w}) (n {y,z}) (n {y,w}) (n {z,w})
    (n {y,z,w}) (n {x,z,w}) (n {x,y,w}) (n {x,y,z})
    ht1 ht2 ht3 ht4 hb1 hb2 hb3 hb4 hb5 hb6 hc1 hc2 hc3 hc4
    hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hsumN
  have hdx := degree_eq_sum_exact_traces F {x,y,z,w} x (by simp)
  change (F.filter (fun S => x ∈ S)).card = ∑ C ∈ ({x,y,z,w} : Finset α).powerset, if x ∈ C then n C else 0 at hdx
  rw [sum_powerset_four _ x y z w hxy hxz hxw hyz hyw hzw] at hdx
  simp [hxy,hxz,hxw] at hdx
  have hdy := degree_eq_sum_exact_traces F {x,y,z,w} y (by simp)
  change (F.filter (fun S => y ∈ S)).card = ∑ C ∈ ({x,y,z,w} : Finset α).powerset, if y ∈ C then n C else 0 at hdy
  rw [sum_powerset_four _ x y z w hxy hxz hxw hyz hyw hzw] at hdy
  simp [Ne.symm hxy,hyz,hyw] at hdy
  have hdz := degree_eq_sum_exact_traces F {x,y,z,w} z (by simp)
  change (F.filter (fun S => z ∈ S)).card = ∑ C ∈ ({x,y,z,w} : Finset α).powerset, if z ∈ C then n C else 0 at hdz
  rw [sum_powerset_four _ x y z w hxy hxz hxw hyz hyw hzw] at hdz
  simp [Ne.symm hxz,Ne.symm hyz,hzw] at hdz
  have hdw := degree_eq_sum_exact_traces F {x,y,z,w} w (by simp)
  change (F.filter (fun S => w ∈ S)).card = ∑ C ∈ ({x,y,z,w} : Finset α).powerset, if w ∈ C then n C else 0 at hdw
  rw [sum_powerset_four _ x y z w hxy hxz hxw hyz hyw hzw] at hdw
  simp [Ne.symm hxw,Ne.symm hyw,Ne.symm hzw] at hdw
  have hdx' : (F.filter (fun S => x ∈ S)).card = 1+n {x}+n {x,y}+n {x,z}+n {x,w}+n {x,z,w}+n {x,y,w}+n {x,y,z} := by
    clear * - hdx h4
    omega
  have hdy' : (F.filter (fun S => y ∈ S)).card = 1+n {y}+n {x,y}+n {y,z}+n {y,w}+n {y,z,w}+n {x,y,w}+n {x,y,z} := by
    clear * - hdy h4
    omega
  have hdz' : (F.filter (fun S => z ∈ S)).card = 1+n {z}+n {x,z}+n {y,z}+n {z,w}+n {y,z,w}+n {x,z,w}+n {x,y,z} := by
    clear * - hdz h4
    omega
  have hdw' : (F.filter (fun S => w ∈ S)).card = 1+n {w}+n {x,w}+n {y,w}+n {z,w}+n {y,z,w}+n {x,z,w}+n {x,y,w} := by
    clear * - hdw h4
    omega
  rw [hdx',hdy',hdz',hdw']
  exact hpat

open Erdos20DegreeCongruences

/-- Every anchor in a hypothetical forty-two-member family has one of three
incompatible global degree-class patterns. -/
theorem forty_two_member_patterns
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : F.card = 42)
    (R : Finset α) (hR : R ∈ F) :
    MemberPattern F R 12 13 ∨ MemberPattern F R 14 17 ∨ MemberPattern F R 15 16 := by
  classical
  obtain ⟨x,y,z,w,hxy,hxz,hxw,hyz,hyw,hzw,hshape⟩ := Finset.card_eq_four.mp (hu R hR)
  subst R
  have hp := forty_two_ordered_degree_pattern F hu hf hi hc x y z w
    hxy hxz hxw hyz hyw hzw hR
  change LocalDegreePattern (degree F x) (degree F y) (degree F z) (degree F w) at hp
  have bridge (l h : ℕ) (hlh : l < h)
      (hx : degree F x=l ∨ degree F x=h)
      (hy : degree F y=l ∨ degree F y=h)
      (hz : degree F z=l ∨ degree F z=h)
      (hw : degree F w=l ∨ degree F w=h)
      (hlo : 2*l+2*h ≤ degree F x+degree F y+degree F z+degree F w)
      (hhi : degree F x+degree F y+degree F z+degree F w ≤ l+3*h) :
      MemberPattern F {x,y,z,w} l h := by
    apply member_pattern_of_degree_sum F {x,y,z,w} l h (hu _ hR) hlh
    · intro q hq
      simp only [Finset.mem_insert,Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hz
      · exact hw
    · simpa [hxy,hxz,hxw,hyz,hyw,hzw,Nat.add_assoc] using hlo
    · simpa [hxy,hxz,hxw,hyz,hyw,hzw,Nat.add_assoc] using hhi
  rcases hp with ⟨hx,hy,hz,hw,hlo,hhi⟩ | ⟨hx,hy,hz,hw,hlo,hhi⟩ | ⟨hx,hy,hz,hw,hlo,hhi⟩
  · exact Or.inl (bridge 12 13 (by decide) hx hy hz hw hlo hhi)
  · exact Or.inr (Or.inl (bridge 14 17 (by decide) hx hy hz hw hlo hhi))
  · exact Or.inr (Or.inr (bridge 15 16 (by decide) hx hy hz hw hlo hhi))

/-- The intersecting rank-four bound improves from forty-two to forty-one. -/
theorem intersecting_rank_four_card_le_forty_one
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) : F.card ≤ 41 := by
  have hb := intersecting_rank_four_card_le_forty_two F hu hf hi
  by_contra hn
  have hc : F.card = 42 := by omega
  exact no_forty_two_degree_patterns F hu hi hc (forty_two_member_patterns F hu hf hi hc)

/-- Two intersecting color classes each satisfy the refined upper bound. -/
theorem rank_four_card_le_eighty_two_of_two_colorable
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hcol : (disjointnessGraph F).Colorable 2) : F.card ≤ 82 := by
  classical
  obtain ⟨c⟩ := hcol
  let classes : Fin 2 → Finset (Finset α) := fun i =>
    (Finset.univ.filter (fun S : F => c S = i)).image Subtype.val
  have hmem : ∀ i S, S ∈ classes i ↔ ∃ hS : S ∈ F, c ⟨S,hS⟩ = i := by
    intro i S
    simp only [classes, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨T, hi, rfl⟩
      exact ⟨T.property, hi⟩
    · rintro ⟨hS, hi⟩
      exact ⟨⟨S,hS⟩, hi, rfl⟩
  have hsub : ∀ i, classes i ⊆ F := by
    intro i S hS
    exact ((hmem i S).mp hS).choose
  have hcap : ∀ i, (classes i).card ≤ 41 := by
    intro i
    apply intersecting_rank_four_card_le_forty_one _
      (fun S hS => hu S (hsub i hS))
      (fun H hH hsun => hf H (hH.trans (hsub i)) hsun)
    intro S hS T hT
    obtain ⟨hSF, hcS⟩ := (hmem i S).mp hS
    obtain ⟨hTF, hcT⟩ := (hmem i T).mp hT
    by_contra hnot
    have hi : S ∩ T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    have hne : (⟨S,hSF⟩ : F) ≠ ⟨T,hTF⟩ := by
      intro heq
      have hv : S = T := congrArg Subtype.val heq
      have he : S = ∅ := by simpa [← hv] using hi
      have hs3 := hu S hSF
      simp [he] at hs3
    exact c.valid (show (disjointnessGraph F).Adj ⟨S,hSF⟩ ⟨T,hTF⟩ from ⟨hne,hi⟩)
      (hcS.trans hcT.symm)
  have hcover : F ⊆ Finset.univ.biUnion classes := by
    intro S hS
    exact Finset.mem_biUnion.mpr ⟨c ⟨S,hS⟩, Finset.mem_univ _,
      (hmem _ S).mpr ⟨hS,rfl⟩⟩
  calc
    _ ≤ (Finset.univ.biUnion classes).card := Finset.card_le_card hcover
    _ ≤ ∑ i, (classes i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin 2, 41 := Finset.sum_le_sum (fun i _ => hcap i)
    _ = 82 := by simp



end Erdos20FortyOne
