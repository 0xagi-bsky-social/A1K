import TerminalSeparation

/-!
Asymmetric terminal separation: the Y component avoids all at-most-two-point
subsets, while the Z component need only avoid all at-most-one-point subsets.
All traces, residual families, cones, and pure-transversal families are the
actual definitions from TerminalSeparation. No I7 classification or bound on
ambient support is used. H27 is a supplied hypothesis only for counting.
-/
namespace FrontierTerminal

universe u
variable {α : Type u} [DecidableEq α]

set_option maxHeartbeats 800000

/-- Supported blocks have no transversal of cardinality at most one. -/
structure OneAvoidance (H : Finset (Finset α)) (W : Finset α) : Prop where
  supported : ∀ T ∈ H, T ⊆ W
  avoids_one : ∀ U : Finset α, U ⊆ W → U.card ≤ 1 →
    ∃ T ∈ H, Disjoint U T

theorem TwoAvoidance.toOneAvoidance
    {H : Finset (Finset α)} {W : Finset α} (h : TwoAvoidance H W) :
    OneAvoidance H W := by
  refine ⟨h.supported, ?_⟩
  intro U hU hc
  exact h.avoids_two U hU (by omega)

/-- The one-point avoidance hypothesis includes the empty-subset case. -/
theorem not_oneAvoidance_empty (W : Finset α) :
    ¬ OneAvoidance (∅ : Finset (Finset α)) W := by
  intro h
  obtain ⟨T, hT, _⟩ := h.avoids_one ∅ (Finset.empty_subset _) (by simp)
  simp at hT

/-- A disjoint residual pair has at least two union points on this support. -/
theorem disjoint_union_trace_ge_two
    (F H : Finset (Finset α)) (x : α) (W : Finset α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hc : HasCones F H x) (hW : OneAvoidance H W)
    (Q P : Finset α) (hQ : Q ∈ residual F x) (hP : P ∈ residual F x)
    (hdis : Disjoint Q P) : 2 ≤ ((Q ∪ P) ∩ W).card := by
  by_contra hn
  obtain ⟨T, hT, hUT⟩ := hW.avoids_one ((Q ∪ P) ∩ W)
    Finset.inter_subset_right (by omega)
  obtain ⟨a, ha⟩ := disjoint_union_meets_blocks F H x hu hf hc Q P hQ hP hdis T hT
  obtain ⟨haU, haT⟩ := Finset.mem_inter.mp ha
  exact Finset.disjoint_left.mp hUT
    (Finset.mem_inter.mpr ⟨haU, hW.supported T hT haT⟩) haT

/-- Asymmetric thresholds three and two force at least five union-trace points. -/
theorem asymmetric_disjoint_union_trace_ge_five
    (F HY HZ : Finset (Finset α)) (x : α) (Y Z : Finset α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hcY : HasCones F HY x) (hcZ : HasCones F HZ x)
    (hY : TwoAvoidance HY Y) (hZ : OneAvoidance HZ Z) (hYZ : Disjoint Y Z)
    (Q P : Finset α) (hQ : Q ∈ residual F x) (hP : P ∈ residual F x)
    (hdis : Disjoint Q P) : 5 ≤ ((Q ∪ P) ∩ (Y ∪ Z)).card := by
  have h3Y := disjoint_union_trace_ge_three F HY x Y hu hf hcY hY Q P hQ hP hdis
  have h2Z := disjoint_union_trace_ge_two F HZ x Z hu hf hcZ hZ Q P hQ hP hdis
  have htr : Disjoint ((Q ∪ P) ∩ Y) ((Q ∪ P) ∩ Z) := by
    rw [Finset.disjoint_left]
    intro a haY haZ
    exact Finset.disjoint_left.mp hYZ
      (Finset.mem_inter.mp haY).2 (Finset.mem_inter.mp haZ).2
  have heq := Finset.card_union_of_disjoint htr
  rw [← Finset.inter_union_distrib_left] at heq
  omega

/-- With a pure Y triple on one side, the other terminal trace lies wholly in Z. -/
theorem asymmetric_opposite_trace_subset_Z
    (F HZ : Finset (Finset α)) (x : α) (Y Z : Finset α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hcZ : HasCones F HZ x) (hZ : OneAvoidance HZ Z) (hYZ : Disjoint Y Z)
    (Q P : Finset α) (hQ : Q ∈ residual F x) (hP : P ∈ residual F x)
    (hQY : PureTriple (Y ∪ Z) Y Q) (htP : TerminalTrace Y Z P)
    (hdis : Disjoint Q P) : P ∩ (Y ∪ Z) ⊆ Z := by
  have h2 := disjoint_union_trace_ge_two F HZ x Z hu hf hcZ hZ Q P hQ hP hdis
  have heQ := pure_trace_opposite_empty hYZ hQY.2
  rw [Finset.union_inter_distrib_right, heQ, Finset.empty_union] at h2
  rcases htP with hsmall | hPY | hPZ
  · have hsub : P ∩ Z ⊆ P ∩ (Y ∪ Z) := by
      intro a ha
      obtain ⟨haP, haZ⟩ := Finset.mem_inter.mp ha
      exact Finset.mem_inter.mpr ⟨haP, Finset.mem_union.mpr (Or.inr haZ)⟩
    have he : P ∩ Z = P ∩ (Y ∪ Z) :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    rw [← he]
    exact Finset.inter_subset_right
  · have heP := pure_trace_opposite_empty hYZ hPY.2
    rw [heP] at h2
    simp at h2
  · exact hPZ.2

/-- In a disjoint terminal pair, any pure Y triple is itself a Y transversal. -/
theorem asymmetric_pureY_is_transversal
    (F HY HZ : Finset (Finset α)) (x : α) (Y Z : Finset α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hcY : HasCones F HY x) (hcZ : HasCones F HZ x)
    (hY : TwoAvoidance HY Y) (hZ : OneAvoidance HZ Z) (hYZ : Disjoint Y Z)
    (Q P : Finset α) (hQ : Q ∈ residual F x) (hP : P ∈ residual F x)
    (hQY : PureTriple (Y ∪ Z) Y Q) (htP : TerminalTrace Y Z P)
    (hdis : Disjoint Q P) : PureTransversal HY (Y ∪ Z) Y Q := by
  have hpZ := asymmetric_opposite_trace_subset_Z F HZ x Y Z hu hf hcZ hZ hYZ
    Q P hQ hP hQY htP hdis
  exact ⟨hQY, pure_trace_meets_own_blocks F HY x Y Z Q P hu hf hcY hY.supported
    hYZ hQ hP hdis hpZ⟩

/-- Every disjoint terminal pair contains an actual pure Y-transversal member. -/
theorem asymmetric_disjoint_terminal_pair_has_pureY_transversal
    (F HY HZ : Finset (Finset α)) (x : α) (Y Z : Finset α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hcY : HasCones F HY x) (hcZ : HasCones F HZ x)
    (hY : TwoAvoidance HY Y) (hZ : OneAvoidance HZ Z) (hYZ : Disjoint Y Z)
    (Q P : Finset α) (hQ : Q ∈ residual F x) (hP : P ∈ residual F x)
    (htQ : TerminalTrace Y Z Q) (htP : TerminalTrace Y Z P)
    (hdis : Disjoint Q P) :
    PureTransversal HY (Y ∪ Z) Y Q ∨ PureTransversal HY (Y ∪ Z) Y P := by
  have h5 := asymmetric_disjoint_union_trace_ge_five
    F HY HZ x Y Z hu hf hcY hcZ hY hZ hYZ Q P hQ hP hdis
  have h3Y := disjoint_union_trace_ge_three F HY x Y hu hf hcY hY Q P hQ hP hdis
  have hle := union_trace_card_le Q P (Y ∪ Z)
  have hQYle : (Q ∩ Y).card ≤ (Q ∩ (Y ∪ Z)).card :=
    Finset.card_le_card (Finset.inter_subset_inter_left (s := Q) Finset.subset_union_left)
  have hPYle : (P ∩ Y).card ≤ (P ∩ (Y ∪ Z)).card :=
    Finset.card_le_card (Finset.inter_subset_inter_left (s := P) Finset.subset_union_left)
  rcases htQ with hsmallQ | hQY | hQZ
  · rcases htP with hsmallP | hPY | hPZ
    · omega
    · right
      exact asymmetric_pureY_is_transversal F HY HZ x Y Z hu hf hcY hcZ hY hZ hYZ
        P Q hP hQ hPY (Or.inl hsmallQ) hdis.symm
    · have heP : P ∩ Y = ∅ := pure_trace_opposite_empty hYZ.symm
        (by simpa only [Finset.union_comm Z Y] using hPZ.2)
      rw [Finset.union_inter_distrib_right, heP, Finset.union_empty] at h3Y
      omega
  · left
    exact asymmetric_pureY_is_transversal F HY HZ x Y Z hu hf hcY hcZ hY hZ hYZ
      Q P hQ hP hQY htP hdis
  · rcases htP with hsmallP | hPY | hPZ
    · have heQ : Q ∩ Y = ∅ := pure_trace_opposite_empty hYZ.symm
        (by simpa only [Finset.union_comm Z Y] using hQZ.2)
      rw [Finset.union_inter_distrib_right, heQ, Finset.empty_union] at h3Y
      omega
    · right
      exact asymmetric_pureY_is_transversal F HY HZ x Y Z hu hf hcY hcZ hY hZ hYZ
        P Q hP hQ hPY (Or.inr (Or.inr hQZ)) hdis.symm
    · have heQ : Q ∩ Y = ∅ := pure_trace_opposite_empty hYZ.symm
        (by simpa only [Finset.union_comm Z Y] using hQZ.2)
      have heP : P ∩ Y = ∅ := pure_trace_opposite_empty hYZ.symm
        (by simpa only [Finset.union_comm Z Y] using hPZ.2)
      rw [Finset.union_inter_distrib_right, heQ, heP] at h3Y
      simp at h3Y

/-- Removing the actual Y-transversal subfamily leaves an intersecting family. -/
theorem asymmetric_without_pureY_intersecting
    (F HY HZ : Finset (Finset α)) (x : α) (Y Z : Finset α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hcY : HasCones F HY x) (hcZ : HasCones F HZ x)
    (hY : TwoAvoidance HY Y) (hZ : OneAvoidance HZ Z) (hYZ : Disjoint Y Z)
    (htrace : ∀ Q ∈ residual F x, TerminalTrace Y Z Q) :
    Intersecting (residual F x \
      pureTransversalMembers (residual F x) HY (Y ∪ Z) Y) := by
  classical
  intro Q hQ P hP
  obtain ⟨hQR, hnQ⟩ := Finset.mem_sdiff.mp hQ
  obtain ⟨hPR, hnP⟩ := Finset.mem_sdiff.mp hP
  by_contra hn
  have hd : Disjoint Q P := Finset.disjoint_iff_inter_eq_empty.mpr
    (Finset.not_nonempty_iff_eq_empty.mp hn)
  rcases asymmetric_disjoint_terminal_pair_has_pureY_transversal
    F HY HZ x Y Z hu hf hcY hcZ hY hZ hYZ Q P hQR hPR
    (htrace Q hQR) (htrace P hPR) hd with h | h
  · exact hnQ (Finset.mem_filter.mpr ⟨hQR, h⟩)
  · exact hnP (Finset.mem_filter.mpr ⟨hPR, h⟩)

/-- The asymmetric terminal bound counts only the Y pure-transversal pool. -/
theorem asymmetric_terminal_separation_card_bound
    (F HY HZ : Finset (Finset α)) (x : α) (Y Z : Finset α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hcY : HasCones F HY x) (hcZ : HasCones F HZ x)
    (hY : TwoAvoidance HY Y) (hZ : OneAvoidance HZ Z) (hYZ : Disjoint Y Z)
    (htrace : ∀ Q ∈ residual F x, TerminalTrace Y Z Q)
    (h27 : H27 α) :
    (residual F x).card ≤ 27 +
      (pureTransversalMembers (residual F x) HY (Y ∪ Z) Y).card := by
  let TY := pureTransversalMembers (residual F x) HY (Y ∪ Z) Y
  have hsub : residual F x \ TY ⊆ F := by
    intro Q hQ
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hQ).1).1
  have hcount : (residual F x \ TY).card ≤ 27 := by
    apply h27 (residual F x \ TY)
    · intro Q hQ
      exact hu Q (hsub hQ)
    · intro G hG hsun
      exact hf G (hG.trans hsub) hsun
    · exact asymmetric_without_pureY_intersecting
        F HY HZ x Y Z hu hf hcY hcZ hY hZ hYZ htrace
  have hpartition := Finset.card_sdiff_add_card_eq_card
    (pureTransversalMembers_subset (residual F x) HY (Y ∪ Z) Y)
  change (residual F x).card ≤ 27 + TY.card
  change (residual F x \ TY).card + TY.card = (residual F x).card at hpartition
  omega

/-- A ten-member bound on the actual removed pool gives residual cardinality 37. -/
theorem asymmetric_terminal_residual_card_le_37
    (F HY HZ : Finset (Finset α)) (x : α) (Y Z : Finset α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hcY : HasCones F HY x) (hcZ : HasCones F HZ x)
    (hY : TwoAvoidance HY Y) (hZ : OneAvoidance HZ Z) (hYZ : Disjoint Y Z)
    (htrace : ∀ Q ∈ residual F x, TerminalTrace Y Z Q)
    (h27 : H27 α)
    (hpool : (pureTransversalMembers (residual F x) HY (Y ∪ Z) Y).card ≤ 10) :
    (residual F x).card ≤ 37 := by
  have := asymmetric_terminal_separation_card_bound
    F HY HZ x Y Z hu hf hcY hcZ hY hZ hYZ htrace h27
  omega

#print axioms asymmetric_disjoint_union_trace_ge_five
#print axioms asymmetric_disjoint_terminal_pair_has_pureY_transversal
#print axioms asymmetric_without_pureY_intersecting
#print axioms asymmetric_terminal_separation_card_bound
#print axioms asymmetric_terminal_residual_card_le_37

end FrontierTerminal
