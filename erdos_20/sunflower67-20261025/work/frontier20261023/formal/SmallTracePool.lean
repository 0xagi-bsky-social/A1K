import TerminalSeparation

/-!
Actual residual members with at most one point on a two-avoiding cone support
form an intersecting family. H27 is supplied only for the cardinality bound.
The incidence-deficit inequality is proved for an arbitrary finite family;
there is no component classification or bound on the ambient ground type.

Prepared as source only. Compilation and the printed axiom reports are to be
performed separately with the existing bounded compilation wrapper.
-/
namespace FrontierTerminal

open scoped BigOperators

universe u
variable {α : Type u} [DecidableEq α]

set_option maxHeartbeats 800000

/-- The actual members whose exact trace on W has size at most one. -/
def smallTracePool (G : Finset (Finset α)) (W : Finset α) : Finset (Finset α) :=
  G.filter (fun Q => (Q ∩ W).card ≤ 1)

/-- The actual members whose exact trace on W is empty. -/
def zeroTracePool (G : Finset (Finset α)) (W : Finset α) : Finset (Finset α) :=
  G.filter (fun Q => (Q ∩ W).card = 0)

/-- Total incidences of members of G with the support W. -/
def traceCardSum (G : Finset (Finset α)) (W : Finset α) : ℕ :=
  ∑ Q ∈ G, (Q ∩ W).card

theorem smallTracePool_subset (G : Finset (Finset α)) (W : Finset α) :
    smallTracePool G W ⊆ G :=
  Finset.filter_subset _ _

theorem zeroTracePool_subset_smallTracePool
    (G : Finset (Finset α)) (W : Finset α) :
    zeroTracePool G W ⊆ smallTracePool G W := by
  intro Q hQ
  obtain ⟨hQG, hzero⟩ := Finset.mem_filter.mp hQ
  exact Finset.mem_filter.mpr ⟨hQG, by omega⟩

/-- Two disjoint members in this pool would have union trace both at most2
and at least3. Coincident members are included in `Intersecting`. -/
theorem residual_smallTracePool_intersecting
    (F H : Finset (Finset α)) (x : α) (W : Finset α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hc : HasCones F H x) (hW : TwoAvoidance H W) :
    Intersecting (smallTracePool (residual F x) W) := by
  intro Q hQ P hP
  obtain ⟨hQR, hQsmall⟩ := Finset.mem_filter.mp hQ
  obtain ⟨hPR, hPsmall⟩ := Finset.mem_filter.mp hP
  by_contra hn
  have hd : Disjoint Q P := Finset.disjoint_iff_inter_eq_empty.mpr
    (Finset.not_nonempty_iff_eq_empty.mp hn)
  have hthree := disjoint_union_trace_ge_three F H x W hu hf hc hW
    Q P hQR hPR hd
  have hupper := union_trace_card_le Q P W
  omega

/-- H27 applies to the actual small-trace subfamily by heredity. -/
theorem residual_smallTracePool_card_le_27
    (F H : Finset (Finset α)) (x : α) (W : Finset α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hc : HasCones F H x) (hW : TwoAvoidance H W) (h27 : H27 α) :
    (smallTracePool (residual F x) W).card ≤ 27 := by
  have hsub : smallTracePool (residual F x) W ⊆ F := by
    intro Q hQ
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hQ).1).1
  apply h27 (smallTracePool (residual F x) W)
  · intro Q hQ
    exact hu Q (hsub hQ)
  · intro G hG hsun
    exact hf G (hG.trans hsub) hsun
  · exact residual_smallTracePool_intersecting F H x W hu hf hc hW

/-- A trace of size0 needs two correction units, size1 needs one, and every
larger trace contributes at least two incidences itself. -/
theorem trace_card_two_deficit (n : ℕ) :
    2 ≤ n + (if n ≤ 1 then 1 else 0) + (if n = 0 then 1 else 0) := by
  split_ifs <;> omega

/-- The actual incidence inequality, requiring no uniformity or sunflower
hypothesis. Zero traces belong to both correcting pools. -/
theorem twice_card_le_trace_sum_add_small_add_zero
    (G : Finset (Finset α)) (W : Finset α) :
    2 * G.card ≤ traceCardSum G W +
      (smallTracePool G W).card + (zeroTracePool G W).card := by
  classical
  induction G using Finset.induction_on with
  | empty => simp [traceCardSum, smallTracePool, zeroTracePool]
  | @insert Q G hQ ih =>
      have hsum : traceCardSum (insert Q G) W =
          (Q ∩ W).card + traceCardSum G W := by
        simp [traceCardSum, hQ]
      have hsmall : (smallTracePool (insert Q G) W).card =
          (smallTracePool G W).card + (if (Q ∩ W).card ≤ 1 then 1 else 0) := by
        by_cases h : (Q ∩ W).card ≤ 1
        · simp [smallTracePool, Finset.filter_insert, h, hQ]
        · simp [smallTracePool, Finset.filter_insert, h, hQ]
      have hzero : (zeroTracePool (insert Q G) W).card =
          (zeroTracePool G W).card + (if (Q ∩ W).card = 0 then 1 else 0) := by
        by_cases h : (Q ∩ W).card = 0
        · have hz : Q ∩ W = ∅ := Finset.card_eq_zero.mp h
          simp [zeroTracePool, Finset.filter_insert, h, hz, hQ]
        · have hz : Q ∩ W ≠ ∅ := by
            intro he
            apply h
            simp [he]
          simp [zeroTracePool, Finset.filter_insert, h, hz, hQ]
      rw [Finset.card_insert_of_not_mem hQ, hsum, hsmall, hzero]
      have hpoint := trace_card_two_deficit (Q ∩ W).card
      omega

/-- Literal residual specialization: no separate numerical r variable hides
which family the inequality counts. -/
theorem residual_twice_card_le_trace_sum_add_small_add_zero
    (F : Finset (Finset α)) (x : α) (W : Finset α) :
    2 * (residual F x).card ≤ traceCardSum (residual F x) W +
      (smallTracePool (residual F x) W).card +
      (zeroTracePool (residual F x) W).card :=
  twice_card_le_trace_sum_add_small_add_zero (residual F x) W

/-- At least52 members, at most66 support incidences and at most27 small
traces force at least11 actual members with empty support trace. -/
theorem zeroTracePool_card_ge_eleven_of_counts
    (G : Finset (Finset α)) (W : Finset α)
    (hcard : 52 ≤ G.card) (hinc : traceCardSum G W ≤ 66)
    (hsmall : (smallTracePool G W).card ≤ 27) :
    11 ≤ (zeroTracePool G W).card := by
  have hcount := twice_card_le_trace_sum_add_small_add_zero G W
  omega

/-- Structural application on arbitrary support: TwoAvoidance and actual
cones prove the small-pool bound; only the two incidence counts are supplied. -/
theorem residual_zeroTracePool_card_ge_eleven
    (F H : Finset (Finset α)) (x : α) (W : Finset α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hc : HasCones F H x) (hW : TwoAvoidance H W) (h27 : H27 α)
    (hcard : 52 ≤ (residual F x).card)
    (hinc : traceCardSum (residual F x) W ≤ 66) :
    11 ≤ (zeroTracePool (residual F x) W).card := by
  apply zeroTracePool_card_ge_eleven_of_counts (residual F x) W hcard hinc
  exact residual_smallTracePool_card_le_27 F H x W hu hf hc hW h27

#print axioms residual_smallTracePool_intersecting
#print axioms residual_smallTracePool_card_le_27
#print axioms twice_card_le_trace_sum_add_small_add_zero
#print axioms residual_twice_card_le_trace_sum_add_small_add_zero
#print axioms zeroTracePool_card_ge_eleven_of_counts
#print axioms residual_zeroTracePool_card_ge_eleven

end FrontierTerminal
