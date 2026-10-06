import SunflowerLean.Erdos20V8Final

namespace Erdos20V9WeightCongruence
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20V8DesignCounts Erdos20V8Boundary Erdos20DegreeCongruences
open Erdos20V8HighWeights Erdos20V8Final

/-- A twenty-triple link with at most one distinguished point in every block
has a reciprocal weight divisible by fifteen. -/
theorem twenty_link_weight_mod_fifteen
    {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hu : ∀ P ∈ L, P.card = 3) (hf : IsSunflowerFree L 3) (hc : L.card = 20)
    (H : Finset α) (hcap : ∀ P ∈ L, (P ∩ H).card ≤ 1) :
    linkWeight L H % 15 = 0 := by
  classical
  let C := H ∩ support L
  have hCI (P : Finset α) (hP : P ∈ L) : P ∩ C = P ∩ H := by
    ext x
    simp only [C,Finset.mem_inter]
    exact ⟨fun h => ⟨h.1,h.2.1⟩,fun h => ⟨h.1,h.2,member_subset_support hP h.1⟩⟩
  have htwo : blockCount L H 2 = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro P hP
    obtain ⟨hPL,hP2⟩ := Finset.mem_filter.mp hP
    have := hcap P hPL
    omega
  have hfirst : blockCount L H 1 = 5 * C.card := by
    have he := block_counts_first_moment L H (fun P hP => (hcap P hP).trans (by decide))
    rw [htwo] at he
    simp only [mul_zero,add_zero] at he
    rw [← he]
    calc
      _ = ∑ P ∈ L, (P ∩ C).card := Finset.sum_congr rfl (fun P hP => congrArg Finset.card (hCI P hP).symm)
      _ = ∑ x ∈ C, (L.filter (fun P => x ∈ P)).card := incidence_sum_eq L C
      _ = ∑ _x ∈ C, 5 := Finset.sum_congr rfl (fun x hx =>
        (Erdos20ExtremalTwenty.extremal_twenty_regular_twelve L hu hf hc).2 x (Finset.mem_inter.mp hx).2)
      _ = _ := by simp [Nat.mul_comm]
  have htotal := block_counts_total L H (fun P hP => (hcap P hP).trans (by decide))
  have hw := linkWeight_eq_block_counts L H (fun P hP => (hcap P hP).trans (by decide))
  rw [hc,htwo] at htotal
  rw [htwo] at hw
  clear * - htotal hw hfirst
  omega

/-- When every member uses at most two high points, every high-point weight
is divisible by fifteen. -/
theorem high_point_weight_mod_fifteen
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (hm : ∀ R ∈ F, (R ∩ highPoints F).card ≤ 2)
    (x : α) (hx : x ∈ highPoints F) :
    pointWeight F (highPoints F) x % 15 = 0 := by
  let L := residualLink F {x}
  have hd : degree F x = 20 := (Finset.mem_filter.mp hx).2
  have huL : ∀ P ∈ L, P.card = 3 := by
    simpa using residualLink_uniform (core := ({x} : Finset α)) hu
  have hfL : IsSunflowerFree L 3 := residualLink_sunflowerFree hf
  have hcL : L.card = 20 := by simpa [L,card_residualLink,upperStar,degree] using hd
  have hcap : ∀ P ∈ L, (P ∩ highPoints F).card ≤ 1 := by
    intro P hP
    obtain ⟨S,hS,hxS,hSP⟩ := mem_residualLink_iff.mp hP
    have hcard := residual_inter_card S (highPoints F) x (Finset.singleton_subset_iff.mp hxS) hx
    have hbound := hm S hS
    rw [hSP] at hcard
    omega
  rw [pointWeight_eq_linkWeight F (highPoints F) x hx]
  exact twenty_link_weight_mod_fifteen L huL hfL hcL (highPoints F) hcap

/-- If high points meet every member once or twice, the family cardinality is
necessarily divisible by five. No all-meeting or cardinality premise is used. -/
theorem card_mod_five_of_high_transversal
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (hm : ∀ R ∈ F, 1 ≤ (R ∩ highPoints F).card ∧ (R ∩ highPoints F).card ≤ 2) :
    F.card % 5 = 0 := by
  have hsum : 15 ∣ ∑ x ∈ highPoints F, pointWeight F (highPoints F) x := by
    apply Finset.dvd_sum
    intro x hx
    exact Nat.dvd_of_mod_eq_zero (high_point_weight_mod_fifteen F hu hf (fun R hR => (hm R hR).2) x hx)
  rw [weighted_high_point_incidence F (highPoints F) (fun R hR => ⟨(hm R hR).1,(hm R hR).2.trans (by decide)⟩)] at hsum
  obtain ⟨k,hk⟩ := hsum
  omega

/-- A bounded rank-four family with only point degrees nineteen/twenty and
cardinality divisible by five has no point of degree nineteen. -/
theorem no_low_points_of_card_mod_five
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hn : F.card ≤ 93)
    (hp : ∀ x ∈ support F, degree F x = 19 ∨ degree F x = 20)
    (hmod : F.card % 5 = 0) : support F = highPoints F := by
  classical
  let A := (support F).filter (fun x => degree F x = 19)
  let B := highPoints F
  have hsplit : A ∪ B = support F := by
    ext x
    simp only [Finset.mem_union,Finset.mem_filter,A,B,highPoints]
    exact ⟨fun h => h.elim And.left And.left,fun hx => (hp x hx).elim (fun h => Or.inl ⟨hx,h⟩) (fun h => Or.inr ⟨hx,h⟩)⟩
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have h19 := (Finset.mem_filter.mp hx).2
    have h20 := (Finset.mem_filter.mp hy).2
    omega
  have hsumA : (∑ x ∈ A, degree F x) = 19*A.card := by
    calc
      _ = ∑ _x ∈ A, 19 := Finset.sum_congr rfl (fun _ hx => (Finset.mem_filter.mp hx).2)
      _ = _ := by simp [Nat.mul_comm]
  have hsumB : (∑ x ∈ B, degree F x) = 20*B.card := by
    calc
      _ = ∑ _x ∈ B, 20 := Finset.sum_congr rfl (fun _ hx => (Finset.mem_filter.mp hx).2)
      _ = _ := by simp [Nat.mul_comm]
  have htotal : 4*F.card = 19*A.card+20*B.card := by
    rw [← hsumA,← hsumB,← Finset.sum_union hdis,hsplit]
    simpa [degree,Nat.mul_comm] using (Erdos20ExtremalSupport.support_degree_sum F 4 hu).symm
  have hz : A.card = 0 := by omega
  have hA : A = ∅ := Finset.card_eq_zero.mp hz
  rw [hA,Finset.empty_union] at hsplit
  exact hsplit.symm

/-- A conditional structural reduction: excluding three high points per member
rules out a nonempty family whose every meeting neighborhood has size56. -/
theorem no_all_meeting_fifty_six_of_high_cap
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3) (hne : F.Nonempty)
    (hcap : ∀ R ∈ F, (R ∩ highPoints F).card ≤ 2)
    (hm : ∀ R ∈ F, (F.filter (fun S => (S ∩ R).Nonempty)).card = 56) : False := by
  have hp := all_meeting_fifty_six_degrees_nineteen_or_twenty F hu hf hm
  have hhit : ∀ R ∈ F, 1 ≤ (R ∩ highPoints F).card ∧ (R ∩ highPoints F).card ≤ 2 := by
    intro R hR
    exact ⟨(Erdos20V8ProfileBridge.meeting_fifty_six_member_structure F hu hf R hR (hm R hR)).2.1.1,hcap R hR⟩
  have hmod := card_mod_five_of_high_transversal F hu hf hhit
  have hbound := Erdos20V7Bounds.rank_four_card_le_ninety_three F hu hf
  have he := no_low_points_of_card_mod_five F hu hbound hp hmod
  obtain ⟨R,hR⟩ := hne
  have hRsub : R ⊆ highPoints F := by rw [← he]; exact member_subset_support hR
  have hc := hcap R hR
  rw [Finset.inter_eq_left.mpr hRsub,hu R hR] at hc
  omega

end Erdos20V9WeightCongruence
