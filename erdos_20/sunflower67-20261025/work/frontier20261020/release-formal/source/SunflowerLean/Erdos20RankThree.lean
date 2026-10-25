import SunflowerLean.Erdos20CrossBounds
import SunflowerLean.Erdos20Research
import Mathlib.Data.Nat.Choose.Sum

/-! Exact trace residues give elementary finite-rank improvements. -/
namespace Erdos20RankThree
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence

/-- Members with a prescribed exact intersection with an anchor. -/
def exactTrace {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (R C : Finset α) : Finset (Finset α) :=
  F.filter (fun S => S ∩ R = C)

/-- A small constructor for a sunflower with three distinct members. -/
theorem sunflower_three_of_intersections {α : Type*} [DecidableEq α]
    (R S T C : Finset α) (hRS : R ≠ S) (hRT : R ≠ T) (hST : S ≠ T)
    (hiRS : R ∩ S = C) (hiRT : R ∩ T = C) (hiST : S ∩ T = C) :
    IsSunflower {R, S, T} 3 := by
  refine ⟨by simp [hRS, hRT, hST], C, ?_⟩
  intro A B hA hB hne
  simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB
  rcases hA with rfl | rfl | rfl <;> rcases hB with rfl | rfl | rfl
  · exact False.elim (hne rfl)
  · exact hiRS
  · exact hiRT
  · simpa [Finset.inter_comm] using hiRS
  · exact False.elim (hne rfl)
  · exact hiST
  · simpa [Finset.inter_comm] using hiRT
  · simpa [Finset.inter_comm] using hiST
  · exact False.elim (hne rfl)

/-- Distinct exact-trace members cannot have disjoint residuals: with the
anchor they would form a sunflower. The proper-core hypothesis is essential. -/
theorem exact_trace_residuals_intersect {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (R C : Finset α) (hR : R ∈ F)
    (hfree : IsSunflowerFree F 3) (hne : C ≠ R)
    (P Q : Finset α) (hP : P ∈ residualLink (exactTrace F R C) C)
    (hQ : Q ∈ residualLink (exactTrace F R C) C) (hPQ : P ≠ Q) :
    (P ∩ Q).Nonempty := by
  obtain ⟨S, hS, hCS, hSP⟩ := mem_residualLink_iff.mp hP
  obtain ⟨T, hT, hCT, hTQ⟩ := mem_residualLink_iff.mp hQ
  obtain ⟨hSF, hSR⟩ := Finset.mem_filter.mp hS
  obtain ⟨hTF, hTR⟩ := Finset.mem_filter.mp hT
  have hRS : R ≠ S := by intro h; subst S; simp at hSR; exact hne hSR.symm
  have hRT : R ≠ T := by intro h; subst T; simp at hTR; exact hne hTR.symm
  have hST : S ≠ T := by intro h; subst T; exact hPQ (hSP.symm.trans hTQ)
  by_contra hn
  have hPQempty : P ∩ Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hi : S ∩ T = C := by
    apply Finset.Subset.antisymm
    · intro x hx
      by_contra hxc
      have hxP : x ∈ P := by rw [← hSP]; exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hx).1, hxc⟩
      have hxQ : x ∈ Q := by rw [← hTQ]; exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hx).2, hxc⟩
      have : x ∈ P ∩ Q := Finset.mem_inter.mpr ⟨hxP, hxQ⟩
      simpa [hPQempty] using this
    · exact fun x hx => Finset.mem_inter.mpr ⟨hCS hx, hCT hx⟩
  apply hfree {R,S,T}
  · intro U hU
    simp only [Finset.mem_insert, Finset.mem_singleton] at hU
    rcases hU with rfl | rfl | rfl <;> assumption
  · exact sunflower_three_of_intersections R S T C hRS hRT hST
      (by simpa [Finset.inter_comm] using hSR)
      (by simpa [Finset.inter_comm] using hTR) hi

/-- Every exact-trace member extends the trace. -/
theorem exact_trace_upperStar {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (R C : Finset α) :
    upperStar (exactTrace F R C) C = exactTrace F R C := by
  apply Finset.filter_eq_self.mpr
  intro S hS
  have h := (Finset.mem_filter.mp hS).2
  rw [← h]
  exact Finset.inter_subset_left

/-- Deleting the exact trace preserves the number of members. -/
theorem exact_trace_card_residual {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (R C : Finset α) :
    (residualLink (exactTrace F R C) C).card = (exactTrace F R C).card := by
  rw [card_residualLink, exact_trace_upperStar]

/-- Sunflower-freeness is inherited by an exact-trace class and its link. -/
theorem exact_trace_residual_free {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (R C : Finset α) (p : ℕ)
    (hfree : IsSunflowerFree F p) :
    IsSunflowerFree (residualLink (exactTrace F R C) C) p := by
  apply residualLink_sunflowerFree
  intro H hH hsun
  exact hfree H (hH.trans (Finset.filter_subset _ _)) hsun



/-- Proper singleton traces at a triple have at most three members. -/
theorem singleton_trace_card_le_three {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (R C : Finset α) (hR : R ∈ F)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hC : C.card = 1) : (exactTrace F R C).card ≤ 3 := by
  have hne : C ≠ R := by intro h; have := hu R hR; rw [← h] at this; omega
  have hur : ∀ P ∈ residualLink (exactTrace F R C) C, P.card = 2 := by
    simpa [hC] using residualLink_uniform
      (fun S hS => hu S (Finset.mem_filter.mp hS).1) (core := C)
  rw [← exact_trace_card_residual]
  apply Erdos20CrossBounds.intersecting_rank_two_three_petals_card_le_three _ hur
    (exact_trace_residual_free F R C 3 hf)
  intro P hP Q hQ
  by_cases hpq : P = Q
  · subst Q
    rw [Finset.inter_self]
    exact Finset.card_pos.mp (by rw [hur P hP]; decide)
  · exact exact_trace_residuals_intersect F R C hR hf hne P Q hP hQ hpq

/-- At most one other triple has a prescribed two-point trace on an anchor. -/
theorem pair_trace_card_le_one {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (R C : Finset α) (hR : R ∈ F)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hsub : C ⊆ R) (hC : C.card = 2) : (exactTrace F R C).card ≤ 1 := by
  have hRnot : R ∉ exactTrace F R C := by
    intro h
    have he : R = C := by simpa using (Finset.mem_filter.mp h).2
    have := hu R hR
    rw [he] at this
    omega
  have hs : insert R (exactTrace F R C) ⊆ Erdos20Research.extensionStar F C := by
    intro S hS
    apply Erdos20Research.mem_extensionStar_iff.mpr
    rcases Finset.mem_insert.mp hS with rfl | hS
    · exact ⟨hR, hsub⟩
    · obtain ⟨hSF, hi⟩ := Finset.mem_filter.mp hS
      exact ⟨hSF, by rw [← hi]; exact Finset.inter_subset_left⟩
  have hlo := Finset.card_le_card hs
  rw [Finset.card_insert_of_notMem hRnot] at hlo
  have hhi := Erdos20Research.extensionStar_card_lt F C 3 3 hu hf (by omega)
  omega

/-- A full-size trace determines its member uniquely. -/
theorem full_trace_card_le_one {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (R C : Finset α)
    (hu : ∀ S ∈ F, S.card = 3) (hC : C.card = 3) :
    (exactTrace F R C).card ≤ 1 := by
  have hs : exactTrace F R C ⊆ {C} := by
    intro S hS
    obtain ⟨hSF, hi⟩ := Finset.mem_filter.mp hS
    have hcS : C ⊆ S := by rw [← hi]; exact Finset.inter_subset_left
    have he : C = S := Finset.eq_of_subset_of_card_le hcS (by rw [hC, hu S hSF])
    simp [he]
  simpa using Finset.card_le_card hs

/-- The members meeting an anchor triple number at most thirteen. -/
theorem meeting_neighborhood_card_le_thirteen {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (R : Finset α) (hR : R ∈ F)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) :
    (F.filter (fun S => (S ∩ R).Nonempty)).card ≤ 13 := by
  classical
  let N := F.filter (fun S => (S ∩ R).Nonempty)
  let w : ℕ → ℕ := fun k => if k = 1 then 3 else if k = 2 ∨ k = 3 then 1 else 0
  have hpart : N.card = ∑ C ∈ R.powerset, (N.filter (fun S => S ∩ R = C)).card :=
    Finset.card_eq_sum_card_fiberwise (fun S _ => Finset.mem_powerset.mpr Finset.inter_subset_right)
  have hcap : ∀ C ∈ R.powerset, (N.filter (fun S => S ∩ R = C)).card ≤ w C.card := by
    intro C hC
    have hsub : C ⊆ R := Finset.mem_powerset.mp hC
    have hc : C.card ≤ 3 := by simpa [hu R hR] using Finset.card_le_card hsub
    have hcomp : N.filter (fun S => S ∩ R = C) ⊆ exactTrace F R C := by
      intro S hS
      obtain ⟨hSN, hi⟩ := Finset.mem_filter.mp hS
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hSN).1, hi⟩
    interval_cases hcc : C.card
    · have he : C = ∅ := Finset.card_eq_zero.mp hcc
      have heN : N.filter (fun S => S ∩ R = C) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro S hS
        obtain ⟨hSN, hi⟩ := Finset.mem_filter.mp hS
        have hn := (Finset.mem_filter.mp hSN).2
        rw [hi, he] at hn
        exact Finset.not_nonempty_empty hn
      simp [heN, w]
    · exact (Finset.card_le_card hcomp).trans (by simpa [w] using singleton_trace_card_le_three F R C hR hu hf hcc)
    · exact (Finset.card_le_card hcomp).trans (by simpa [w] using pair_trace_card_le_one F R C hR hu hf hsub hcc)
    · exact (Finset.card_le_card hcomp).trans (by simpa [w] using full_trace_card_le_one F R C hu hcc)
  calc
    _ = N.card := rfl
    _ ≤ ∑ C ∈ R.powerset, w C.card := by rw [hpart]; exact Finset.sum_le_sum hcap
    _ = 13 := by rw [Finset.sum_powerset_apply_card, hu R hR]; norm_num [w, Finset.sum_range_succ]



/-- In an intersecting family, a two-point trace reduces the opposite
singleton trace from three possible members to at most two. -/
theorem opposite_traces_sum_le_three {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (R : Finset α) (x : α) (hR : R ∈ F) (hx : x ∈ R)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) :
    (exactTrace F R {x}).card + (exactTrace F R (R.erase x)).card ≤ 3 := by
  have hc : (R.erase x).card = 2 := by rw [Finset.card_erase_of_mem hx, hu R hR]
  have hp := pair_trace_card_le_one F R (R.erase x) hR hu hf (Finset.erase_subset _ _) hc
  by_cases he : (exactTrace F R (R.erase x)).Nonempty
  · obtain ⟨T, hT⟩ := he
    obtain ⟨hTF, hTR⟩ := Finset.mem_filter.mp hT
    have hxc : x ∉ T := by
      intro hxT
      have : x ∈ T ∩ R := Finset.mem_inter.mpr ⟨hxT, hx⟩
      rw [hTR] at this
      exact Finset.notMem_erase x R this
    have hTdiff : (T \ R).card = 1 := by
      rw [Finset.card_sdiff, hu T hTF, Finset.inter_comm R T, hTR, hc]
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hTdiff
    have hvout : v ∉ R := by
      have : v ∈ T \ R := by rw [hv]; simp
      exact (Finset.mem_sdiff.mp this).2
    have hur : ∀ P ∈ residualLink (exactTrace F R {x}) {x}, P.card = 2 := by
      simpa using residualLink_uniform
        (fun S hS => hu S (Finset.mem_filter.mp hS).1) (core := {x})
    have hcommon : ∀ P ∈ residualLink (exactTrace F R {x}) {x}, v ∈ P := by
      intro P hP
      obtain ⟨S, hS, hCS, hSP⟩ := mem_residualLink_iff.mp hP
      obtain ⟨hSF, hSR⟩ := Finset.mem_filter.mp hS
      obtain ⟨z, hz⟩ := hi S hSF T hTF
      obtain ⟨hzS, hzT⟩ := Finset.mem_inter.mp hz
      have hzout : z ∉ R := by
        intro hzR
        have : z = x := by
          have hzSR : z ∈ S ∩ R := Finset.mem_inter.mpr ⟨hzS, hzR⟩
          simpa [hSR] using hzSR
        exact hxc (this ▸ hzT)
      have hzv : z = v := by
        have : z ∈ T \ R := Finset.mem_sdiff.mpr ⟨hzT, hzout⟩
        simpa [hv] using this
      rw [← hSP]
      exact Finset.mem_sdiff.mpr ⟨hzv ▸ hzS, by simpa using (fun h : v = x => hvout (h ▸ hx))⟩
    have hb := Erdos20CrossBounds.common_point_rank_two_three_petals_card_le_two
      (residualLink (exactTrace F R {x}) {x}) hur (exact_trace_residual_free F R {x} 3 hf) v hcommon
    rw [exact_trace_card_residual] at hb
    omega
  · have he0 : exactTrace F R (R.erase x) = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    rw [he0]
    simpa using singleton_trace_card_le_three F R {x} hR hu hf (by simp)



/-- Every nonempty proper subset of a triple is a singleton or its opposite pair. -/
theorem nonempty_proper_subset_triple {α : Type*} [DecidableEq α]
    (R C : Finset α) (hR : R.card = 3) (hsub : C ⊆ R)
    (hne : C.Nonempty) (hproper : C ≠ R) :
    ∃ x ∈ R, C = {x} ∨ C = R.erase x := by
  have hcle := Finset.card_le_card hsub
  have hclt : C.card < 3 := by
    by_contra hn
    exact hproper (Finset.eq_of_subset_of_card_le hsub (by omega))
  have hcp := hne.card_pos
  have hcases : C.card = 1 ∨ C.card = 2 := by omega
  rcases hcases with hc | hc
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc
    exact ⟨x, hsub (by simp [hx]), Or.inl hx⟩
  · have hdiff : (R \ C).card = 1 := by rw [Finset.card_sdiff_of_subset hsub, hR, hc]
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hdiff
    have hxin : x ∈ R \ C := by rw [hx]; simp
    obtain ⟨hxR, hxC⟩ := Finset.mem_sdiff.mp hxin
    refine ⟨x, hxR, Or.inr ?_⟩
    ext y
    constructor
    · intro hy
      exact Finset.mem_erase.mpr ⟨fun hyx => hxC (hyx ▸ hy), hsub hy⟩
    · intro hy
      obtain ⟨hyx, hyR⟩ := Finset.mem_erase.mp hy
      by_contra hyC
      have : y ∈ R \ C := Finset.mem_sdiff.mpr ⟨hyR, hyC⟩
      have hyx' : y = x := by simpa [hx] using this
      exact hyx hyx'

/-- A triple meeting every member organizes the family into three opposite-trace
pairs and the anchor itself. -/
theorem anchor_trace_cover {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (R : Finset α) (hR : R ∈ F)
    (hu : ∀ S ∈ F, S.card = 3)
    (hhit : ∀ S ∈ F, (S ∩ R).Nonempty) :
    F ⊆ insert R (R.biUnion (fun x => exactTrace F R {x} ∪ exactTrace F R (R.erase x))) := by
  intro S hS
  by_cases he : S ∩ R = R
  · have hs : R ⊆ S := by rw [← he]; exact Finset.inter_subset_left
    have hRS : R = S := Finset.eq_of_subset_of_card_le hs (by rw [hu R hR, hu S hS])
    simp [hRS]
  · obtain ⟨x, hx, hcase⟩ := nonempty_proper_subset_triple R (S ∩ R) (hu R hR)
      Finset.inter_subset_right (hhit S hS) he
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    refine ⟨x, hx, ?_⟩
    rcases hcase with hcase | hcase
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hS, hcase⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hS, hcase⟩)

/-- The sharp bound for intersecting three-uniform three-sunflower-free families. -/
theorem intersecting_rank_three_card_le_ten {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S ∈ F, S.card = 3)
    (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) : F.card ≤ 10 := by
  classical
  by_cases hne : F.Nonempty
  · obtain ⟨R, hR⟩ := hne
    have hcover := anchor_trace_cover F R hR hu (fun S hS => hi S hS R hR)
    calc
      F.card ≤ (insert R (R.biUnion (fun x => exactTrace F R {x} ∪ exactTrace F R (R.erase x)))).card := Finset.card_le_card hcover
      _ ≤ (R.biUnion (fun x => exactTrace F R {x} ∪ exactTrace F R (R.erase x))).card + 1 := Finset.card_insert_le _ _
      _ ≤ (∑ x ∈ R, (exactTrace F R {x} ∪ exactTrace F R (R.erase x)).card) + 1 := Nat.add_le_add_right Finset.card_biUnion_le 1
      _ ≤ (∑ x ∈ R, ((exactTrace F R {x}).card + (exactTrace F R (R.erase x)).card)) + 1 := by
        exact Nat.add_le_add_right (Finset.sum_le_sum (fun x _ => Finset.card_union_le _ _)) 1
      _ ≤ (∑ _x ∈ R, 3) + 1 := by
        exact Nat.add_le_add_right (Finset.sum_le_sum (fun x hx => opposite_traces_sum_le_three F R x hR hx hu hf hi)) 1
      _ = 10 := by simp [hu R hR]
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

/-- Members disjoint from one nonempty anchor pairwise intersect, otherwise
three disjoint members would be a sunflower. -/
theorem disjoint_anchor_family_intersecting {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (R : Finset α) (hR : R ∈ F)
    (hneR : R.Nonempty) (hf : IsSunflowerFree F 3)
    (S : Finset α) (hS : S ∈ F.filter (fun S => S ∩ R = ∅))
    (T : Finset α) (hT : T ∈ F.filter (fun T => T ∩ R = ∅))
    (hneS : S.Nonempty) (hneT : T.Nonempty) : (S ∩ T).Nonempty := by
  obtain ⟨hSF, hSR⟩ := Finset.mem_filter.mp hS
  obtain ⟨hTF, hTR⟩ := Finset.mem_filter.mp hT
  by_contra hn
  have hST : S ∩ T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hRSne : R ≠ S := by intro h; subst S; simp at hSR; exact (Finset.nonempty_iff_ne_empty.mp hneR) hSR
  have hRTne : R ≠ T := by intro h; subst T; simp at hTR; exact (Finset.nonempty_iff_ne_empty.mp hneR) hTR
  have hSTne : S ≠ T := by intro h; subst T; simp at hST; exact (Finset.nonempty_iff_ne_empty.mp hneS) hST
  apply hf {R,S,T}
  · intro U hU
    simp only [Finset.mem_insert, Finset.mem_singleton] at hU
    rcases hU with rfl | rfl | rfl <;> assumption
  · exact sunflower_three_of_intersections R S T ∅ hRSne hRTne hSTne
      (by simpa [Finset.inter_comm] using hSR) (by simpa [Finset.inter_comm] using hTR) hST

/-- An unconditional improvement of the elementary thirty-two bound to
 twenty-three; the sharper literature value twenty is not asserted here. -/
theorem rank_three_three_petals_card_le_twenty_three {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S ∈ F, S.card = 3)
    (hf : IsSunflowerFree F 3) : F.card ≤ 23 := by
  classical
  by_cases hne : F.Nonempty
  · obtain ⟨R, hR⟩ := hne
    let D := F.filter (fun S => S ∩ R = ∅)
    have huD : ∀ S ∈ D, S.card = 3 := fun S hS => hu S (Finset.mem_filter.mp hS).1
    have hfD : IsSunflowerFree D 3 := fun H hH hsun => hf H (hH.trans (Finset.filter_subset _ _)) hsun
    have hiD : ∀ S ∈ D, ∀ T ∈ D, (S ∩ T).Nonempty := by
      intro S hS T hT
      exact disjoint_anchor_family_intersecting F R hR
        (Finset.card_pos.mp (by rw [hu R hR]; decide)) hf S hS T hT
        (Finset.card_pos.mp (by rw [huD S hS]; decide))
        (Finset.card_pos.mp (by rw [huD T hT]; decide))
    have hd := intersecting_rank_three_card_le_ten D huD hfD hiD
    have hn := meeting_neighborhood_card_le_thirteen F R hR hu hf
    have hsplit : F.card = (F.filter (fun S => (S ∩ R).Nonempty)).card + D.card := by
      have hs := Finset.filter_card_add_filter_neg_card_eq_card (s := F) (p := fun S => (S ∩ R).Nonempty)
      simpa [D, Finset.not_nonempty_iff_eq_empty] using hs.symm
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

end Erdos20RankThree
