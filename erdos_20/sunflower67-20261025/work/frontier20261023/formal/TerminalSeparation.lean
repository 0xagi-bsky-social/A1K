import AHS27Data

/-!
Terminal separation on arbitrary ground types.  The only structural input is
two disjoint supports carrying prescribed cones and blocks avoiding every
subset of at most two support points.  No finite support cutoff, completeness
of the centre link, or classification theorem is assumed.  H27 is an explicit
hypothesis only in the cardinality corollaries.
-/
namespace FrontierTerminal

universe u
variable {α : Type u} [DecidableEq α]

set_option maxHeartbeats 800000

/-- Actual members avoiding the distinguished centre. -/
def residual (F : Finset (Finset α)) (x : α) : Finset (Finset α) :=
  F.filter (fun Q => x ∉ Q)

/-- Blocks are supported on W, and every at-most-two-point subset misses one. -/
structure TwoAvoidance (H : Finset (Finset α)) (W : Finset α) : Prop where
  supported : ∀ T ∈ H, T ⊆ W
  avoids_two : ∀ U : Finset α, U ⊆ W → U.card ≤ 2 →
    ∃ T ∈ H, Disjoint U T

/-- Every component block has its cone in the actual family. -/
def HasCones (F H : Finset (Finset α)) (x : α) : Prop :=
  ∀ T ∈ H, insert x T ∈ F

/-- Nonempty intersections are required also when the two members coincide. -/
def Intersecting (G : Finset (Finset α)) : Prop :=
  ∀ Q ∈ G, ∀ P ∈ G, (Q ∩ P).Nonempty

/-- A pure triple is the entire support trace, not just a contained triple. -/
def PureTriple (S W Q : Finset α) : Prop :=
  (Q ∩ S).card = 3 ∧ Q ∩ S ⊆ W

def PureTransversal (H : Finset (Finset α)) (S W Q : Finset α) : Prop :=
  PureTriple S W Q ∧ ∀ T ∈ H, ((Q ∩ S) ∩ T).Nonempty

def TerminalTrace (Y Z Q : Finset α) : Prop :=
  (Q ∩ (Y ∪ Z)).card ≤ 2 ∨
    PureTriple (Y ∪ Z) Y Q ∨ PureTriple (Y ∪ Z) Z Q

/-- The intersecting rank-four bound is supplied, not declared as an axiom. -/
def H27 (α : Type u) [DecidableEq α] : Prop :=
  ∀ G : Finset (Finset α), (∀ Q ∈ G, Q.card = 4) →
    IsSunflowerFree G 3 → Intersecting G → G.card ≤ 27

theorem terminalTrace_literal (Y Z Q : Finset α) :
    TerminalTrace Y Z Q ↔
      (Q ∩ (Y ∪ Z)).card ≤ 2 ∨
      ((Q ∩ (Y ∪ Z)).card = 3 ∧ Q ∩ (Y ∪ Z) ⊆ Y) ∨
      ((Q ∩ (Y ∪ Z)).card = 3 ∧ Q ∩ (Y ∪ Z) ⊆ Z) := Iff.rfl

/-- Avoidance excludes an empty block family, even for an empty support. -/
theorem not_twoAvoidance_empty (W : Finset α) :
    ¬ TwoAvoidance (∅ : Finset (Finset α)) W := by
  intro h
  obtain ⟨T, hT, _⟩ := h.avoids_two ∅ (Finset.empty_subset _) (by simp)
  simpa using hT

/-- A disjoint residual pair must meet every prescribed block in its union. -/
theorem disjoint_union_meets_blocks
    (F H : Finset (Finset α)) (x : α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hc : HasCones F H x)
    (Q P : Finset α) (hQ : Q ∈ residual F x) (hP : P ∈ residual F x)
    (hdis : Disjoint Q P) : ∀ T ∈ H, ((Q ∪ P) ∩ T).Nonempty := by
  obtain ⟨hQF, hxQ⟩ := Finset.mem_filter.mp hQ
  obtain ⟨hPF, hxP⟩ := Finset.mem_filter.mp hP
  intro T hT
  by_contra hn
  have he : (Q ∪ P) ∩ T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hQT : Disjoint Q (insert x T) := by
    rw [Finset.disjoint_left]
    intro a haQ haT
    rcases Finset.mem_insert.mp haT with rfl | haT
    · exact hxQ haQ
    · have ha : a ∈ (Q ∪ P) ∩ T :=
        Finset.mem_inter.mpr ⟨Finset.mem_union.mpr (Or.inl haQ), haT⟩
      simpa [he] using ha
  have hPT : Disjoint P (insert x T) := by
    rw [Finset.disjoint_left]
    intro a haP haT
    rcases Finset.mem_insert.mp haT with rfl | haT
    · exact hxP haP
    · have ha : a ∈ (Q ∪ P) ∩ T :=
        Finset.mem_inter.mpr ⟨Finset.mem_union.mpr (Or.inr haP), haT⟩
      simpa [he] using ha
  have hQP : Q ≠ P := by
    intro heq
    subst P
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < Q.card by rw [hu Q hQF]; omega)
    exact Finset.disjoint_left.mp hdis ha ha
  have hQC : Q ≠ insert x T := by
    intro heq
    apply hxQ
    rw [heq]
    exact Finset.mem_insert_self _ _
  have hPC : P ≠ insert x T := by
    intro heq
    apply hxP
    rw [heq]
    exact Finset.mem_insert_self _ _
  apply hf {Q, P, insert x T}
  · intro A hA
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl
    · exact hQF
    · exact hPF
    · exact hc T hT
  · exact Erdos20RankThree.sunflower_three_of_intersections
      Q P (insert x T) ∅ hQP hQC hPC
      (Finset.disjoint_iff_inter_eq_empty.mp hdis)
      (Finset.disjoint_iff_inter_eq_empty.mp hQT)
      (Finset.disjoint_iff_inter_eq_empty.mp hPT)

/-- Each supported component contributes at least three union-trace points. -/
theorem disjoint_union_trace_ge_three
    (F H : Finset (Finset α)) (x : α) (W : Finset α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hc : HasCones F H x) (hW : TwoAvoidance H W)
    (Q P : Finset α) (hQ : Q ∈ residual F x) (hP : P ∈ residual F x)
    (hdis : Disjoint Q P) : 3 ≤ ((Q ∪ P) ∩ W).card := by
  by_contra hn
  obtain ⟨T, hT, hUT⟩ := hW.avoids_two ((Q ∪ P) ∩ W)
    Finset.inter_subset_right (by omega)
  obtain ⟨a, ha⟩ := disjoint_union_meets_blocks F H x hu hf hc Q P hQ hP hdis T hT
  obtain ⟨haU, haT⟩ := Finset.mem_inter.mp ha
  exact Finset.disjoint_left.mp hUT
    (Finset.mem_inter.mpr ⟨haU, hW.supported T hT haT⟩) haT

/-- Disjoint residuals use at least six points of the two disjoint supports. -/
theorem disjoint_union_trace_ge_six
    (F HY HZ : Finset (Finset α)) (x : α) (Y Z : Finset α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hcY : HasCones F HY x) (hcZ : HasCones F HZ x)
    (hY : TwoAvoidance HY Y) (hZ : TwoAvoidance HZ Z) (hYZ : Disjoint Y Z)
    (Q P : Finset α) (hQ : Q ∈ residual F x) (hP : P ∈ residual F x)
    (hdis : Disjoint Q P) : 6 ≤ ((Q ∪ P) ∩ (Y ∪ Z)).card := by
  have h3Y := disjoint_union_trace_ge_three F HY x Y hu hf hcY hY Q P hQ hP hdis
  have h3Z := disjoint_union_trace_ge_three F HZ x Z hu hf hcZ hZ Q P hQ hP hdis
  have htr : Disjoint ((Q ∪ P) ∩ Y) ((Q ∪ P) ∩ Z) := by
    rw [Finset.disjoint_left]
    intro a haY haZ
    exact Finset.disjoint_left.mp hYZ
      (Finset.mem_inter.mp haY).2 (Finset.mem_inter.mp haZ).2
  have heq := Finset.card_union_of_disjoint htr
  rw [← Finset.inter_union_distrib_left] at heq
  omega

/-- The small-union criterion: at most five support points force intersection. -/
theorem small_union_intersects
    (F HY HZ : Finset (Finset α)) (x : α) (Y Z : Finset α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hcY : HasCones F HY x) (hcZ : HasCones F HZ x)
    (hY : TwoAvoidance HY Y) (hZ : TwoAvoidance HZ Z) (hYZ : Disjoint Y Z)
    (Q P : Finset α) (hQ : Q ∈ residual F x) (hP : P ∈ residual F x)
    (hsmall : ((Q ∪ P) ∩ (Y ∪ Z)).card ≤ 5) : (Q ∩ P).Nonempty := by
  by_contra hn
  have hd : Disjoint Q P := Finset.disjoint_iff_inter_eq_empty.mpr
    (Finset.not_nonempty_iff_eq_empty.mp hn)
  have := disjoint_union_trace_ge_six F HY HZ x Y Z hu hf hcY hcZ hY hZ hYZ
    Q P hQ hP hd
  omega

theorem union_trace_card_le (Q P S : Finset α) :
    ((Q ∪ P) ∩ S).card ≤ (Q ∩ S).card + (P ∩ S).card := by
  rw [Finset.union_inter_distrib_right]
  exact Finset.card_union_le _ _

/-- Mixed pairs are permitted: only the total trace size is restricted. -/
theorem residual_intersecting_of_trace_le_two
    (F HY HZ : Finset (Finset α)) (x : α) (Y Z : Finset α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hcY : HasCones F HY x) (hcZ : HasCones F HZ x)
    (hY : TwoAvoidance HY Y) (hZ : TwoAvoidance HZ Z) (hYZ : Disjoint Y Z)
    (htrace : ∀ Q ∈ residual F x, (Q ∩ (Y ∪ Z)).card ≤ 2) :
    Intersecting (residual F x) := by
  intro Q hQ P hP
  apply small_union_intersects F HY HZ x Y Z hu hf hcY hcZ hY hZ hYZ Q P hQ hP
  have hq := htrace Q hQ
  have hp := htrace P hP
  have he := union_trace_card_le Q P (Y ∪ Z)
  omega

theorem terminalTrace_card_le_three {Y Z Q : Finset α}
    (h : TerminalTrace Y Z Q) : (Q ∩ (Y ∪ Z)).card ≤ 3 := by
  rcases h with h | h | h
  · omega
  · exact Nat.le_of_eq h.1
  · exact Nat.le_of_eq h.1

theorem pure_trace_opposite_empty {Y Z Q : Finset α} (hYZ : Disjoint Y Z)
    (hQ : Q ∩ (Y ∪ Z) ⊆ Y) : Q ∩ Z = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨haQ, haZ⟩ := Finset.mem_inter.mp ha
  have haY := hQ (Finset.mem_inter.mpr
    ⟨haQ, Finset.mem_union.mpr (Or.inr haZ)⟩)
  exact Finset.disjoint_left.mp hYZ haY haZ

/-- For opposing pure traces, the union-transversal condition belongs to each side. -/
theorem pure_trace_meets_own_blocks
    (F H : Finset (Finset α)) (x : α) (Y Z Q P : Finset α)
    (hu : ∀ A ∈ F, A.card = 4) (hf : IsSunflowerFree F 3)
    (hc : HasCones F H x) (hs : ∀ T ∈ H, T ⊆ Y) (hYZ : Disjoint Y Z)
    (hQ : Q ∈ residual F x) (hP : P ∈ residual F x) (hdis : Disjoint Q P)
    (hpureP : P ∩ (Y ∪ Z) ⊆ Z) :
    ∀ T ∈ H, ((Q ∩ (Y ∪ Z)) ∩ T).Nonempty := by
  intro T hT
  obtain ⟨a, ha⟩ := disjoint_union_meets_blocks F H x hu hf hc Q P hQ hP hdis T hT
  obtain ⟨haU, haT⟩ := Finset.mem_inter.mp ha
  have haY := hs T hT haT
  rcases Finset.mem_union.mp haU with haQ | haP
  · exact ⟨a, Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr
      ⟨haQ, Finset.mem_union.mpr (Or.inl haY)⟩, haT⟩⟩
  · have haZ := hpureP (Finset.mem_inter.mpr
      ⟨haP, Finset.mem_union.mpr (Or.inl haY)⟩)
    exact False.elim (Finset.disjoint_left.mp hYZ haY haZ)

/-- Every disjoint terminal pair is an opposing pair of pure transversals. -/
theorem disjoint_terminal_pair_opposing
    (F HY HZ : Finset (Finset α)) (x : α) (Y Z : Finset α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hcY : HasCones F HY x) (hcZ : HasCones F HZ x)
    (hY : TwoAvoidance HY Y) (hZ : TwoAvoidance HZ Z) (hYZ : Disjoint Y Z)
    (Q P : Finset α) (hQ : Q ∈ residual F x) (hP : P ∈ residual F x)
    (htQ : TerminalTrace Y Z Q) (htP : TerminalTrace Y Z P)
    (hdis : Disjoint Q P) :
    (PureTransversal HY (Y ∪ Z) Y Q ∧ PureTransversal HZ (Y ∪ Z) Z P) ∨
    (PureTransversal HZ (Y ∪ Z) Z Q ∧ PureTransversal HY (Y ∪ Z) Y P) := by
  have h6 := disjoint_union_trace_ge_six F HY HZ x Y Z hu hf hcY hcZ hY hZ hYZ
    Q P hQ hP hdis
  have hle := union_trace_card_le Q P (Y ∪ Z)
  have hQ3 := terminalTrace_card_le_three htQ
  have hP3 := terminalTrace_card_le_three htP
  have hQpure : PureTriple (Y ∪ Z) Y Q ∨ PureTriple (Y ∪ Z) Z Q := by
    rcases htQ with h | h | h
    · omega
    · exact Or.inl h
    · exact Or.inr h
  have hPpure : PureTriple (Y ∪ Z) Y P ∨ PureTriple (Y ∪ Z) Z P := by
    rcases htP with h | h | h
    · omega
    · exact Or.inl h
    · exact Or.inr h
  rcases hQpure with hQY | hQZ <;> rcases hPpure with hPY | hPZ
  · have h3 := disjoint_union_trace_ge_three F HZ x Z hu hf hcZ hZ Q P hQ hP hdis
    have heQ := pure_trace_opposite_empty hYZ hQY.2
    have heP := pure_trace_opposite_empty hYZ hPY.2
    rw [Finset.union_inter_distrib_right, heQ, heP] at h3
    simp at h3
  · left
    constructor
    · exact ⟨hQY, pure_trace_meets_own_blocks F HY x Y Z Q P hu hf hcY hY.supported
        hYZ hQ hP hdis hPZ.2⟩
    · refine ⟨hPZ, ?_⟩
      simpa only [Finset.union_comm Z Y] using
        pure_trace_meets_own_blocks F HZ x Z Y P Q hu hf hcZ hZ.supported
          hYZ.symm hP hQ hdis.symm (by simpa only [Finset.union_comm Z Y] using hQY.2)
  · right
    constructor
    · refine ⟨hQZ, ?_⟩
      simpa only [Finset.union_comm Z Y] using
        pure_trace_meets_own_blocks F HZ x Z Y Q P hu hf hcZ hZ.supported
          hYZ.symm hQ hP hdis (by simpa only [Finset.union_comm Z Y] using hPY.2)
    · exact ⟨hPY, pure_trace_meets_own_blocks F HY x Y Z P Q hu hf hcY hY.supported
        hYZ hP hQ hdis.symm hQZ.2⟩
  · have h3 := disjoint_union_trace_ge_three F HY x Y hu hf hcY hY Q P hQ hP hdis
    have heQ : Q ∩ Y = ∅ := pure_trace_opposite_empty hYZ.symm
      (by simpa only [Finset.union_comm Z Y] using hQZ.2)
    have heP : P ∩ Y = ∅ := pure_trace_opposite_empty hYZ.symm
      (by simpa only [Finset.union_comm Z Y] using hPZ.2)
    rw [Finset.union_inter_distrib_right, heQ, heP] at h3
    simp at h3

/-- If either side has no pure transversal member, the residual family intersects. -/
theorem residual_intersecting_of_no_pureY_transversal
    (F HY HZ : Finset (Finset α)) (x : α) (Y Z : Finset α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hcY : HasCones F HY x) (hcZ : HasCones F HZ x)
    (hY : TwoAvoidance HY Y) (hZ : TwoAvoidance HZ Z) (hYZ : Disjoint Y Z)
    (htrace : ∀ Q ∈ residual F x, TerminalTrace Y Z Q)
    (hnone : ∀ Q ∈ residual F x, ¬ PureTransversal HY (Y ∪ Z) Y Q) :
    Intersecting (residual F x) := by
  intro Q hQ P hP
  by_contra hn
  have hd : Disjoint Q P := Finset.disjoint_iff_inter_eq_empty.mpr
    (Finset.not_nonempty_iff_eq_empty.mp hn)
  rcases disjoint_terminal_pair_opposing F HY HZ x Y Z hu hf hcY hcZ hY hZ hYZ
    Q P hQ hP (htrace Q hQ) (htrace P hP) hd with h | h
  · exact hnone Q hQ h.1
  · exact hnone P hP h.2

/-- The D19 terminal shape permits arbitrary pure Z triples and mixed pairs. -/
theorem residual_intersecting_of_no_pureY
    (F HY HZ : Finset (Finset α)) (x : α) (Y Z : Finset α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hcY : HasCones F HY x) (hcZ : HasCones F HZ x)
    (hY : TwoAvoidance HY Y) (hZ : TwoAvoidance HZ Z) (hYZ : Disjoint Y Z)
    (htrace : ∀ Q ∈ residual F x,
      (Q ∩ (Y ∪ Z)).card ≤ 2 ∨ PureTriple (Y ∪ Z) Z Q) :
    Intersecting (residual F x) := by
  apply residual_intersecting_of_no_pureY_transversal
    F HY HZ x Y Z hu hf hcY hcZ hY hZ hYZ
  · intro Q hQ
    rcases htrace Q hQ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · intro Q hQ hPY
    rcases htrace Q hQ with h | hPZ
    · have hc := hPY.1.1
      omega
    · have he : Q ∩ (Y ∪ Z) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        exact Finset.disjoint_left.mp hYZ (hPY.1.2 ha) (hPZ.2 ha)
      have hc := hPY.1.1
      rw [he] at hc
      simp at hc

theorem residual_card_le_27_of_intersecting
    (F : Finset (Finset α)) (x : α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (h27 : H27 α) (hi : Intersecting (residual F x)) :
    (residual F x).card ≤ 27 := by
  apply h27 (residual F x)
  · intro Q hQ
    exact hu Q (Finset.mem_filter.mp hQ).1
  · intro G hG hsun
    exact hf G (hG.trans (Finset.filter_subset _ _)) hsun
  · exact hi

theorem residual_card_le_27_of_trace_le_two
    (F HY HZ : Finset (Finset α)) (x : α) (Y Z : Finset α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hcY : HasCones F HY x) (hcZ : HasCones F HZ x)
    (hY : TwoAvoidance HY Y) (hZ : TwoAvoidance HZ Z) (hYZ : Disjoint Y Z)
    (htrace : ∀ Q ∈ residual F x, (Q ∩ (Y ∪ Z)).card ≤ 2)
    (h27 : H27 α) : (residual F x).card ≤ 27 :=
  residual_card_le_27_of_intersecting F x hu hf h27
    (residual_intersecting_of_trace_le_two F HY HZ x Y Z hu hf hcY hcZ hY hZ hYZ htrace)

theorem residual_card_le_27_of_no_pureY
    (F HY HZ : Finset (Finset α)) (x : α) (Y Z : Finset α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hcY : HasCones F HY x) (hcZ : HasCones F HZ x)
    (hY : TwoAvoidance HY Y) (hZ : TwoAvoidance HZ Z) (hYZ : Disjoint Y Z)
    (htrace : ∀ Q ∈ residual F x,
      (Q ∩ (Y ∪ Z)).card ≤ 2 ∨ PureTriple (Y ∪ Z) Z Q)
    (h27 : H27 α) : (residual F x).card ≤ 27 :=
  residual_card_le_27_of_intersecting F x hu hf h27
    (residual_intersecting_of_no_pureY F HY HZ x Y Z hu hf hcY hcZ hY hZ hYZ htrace)

/-- The actual pure-transversal members in a specified component. -/
noncomputable def pureTransversalMembers
    (R H : Finset (Finset α)) (S W : Finset α) : Finset (Finset α) := by
  classical
  exact R.filter (PureTransversal H S W)

theorem pureTransversalMembers_subset
    (R H : Finset (Finset α)) (S W : Finset α) :
    pureTransversalMembers R H S W ⊆ R := by
  classical
  exact Finset.filter_subset _ _

/-- Deleting either transversal side leaves an intersecting family. -/
theorem terminal_without_pureY_intersecting
    (F HY HZ : Finset (Finset α)) (x : α) (Y Z : Finset α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hcY : HasCones F HY x) (hcZ : HasCones F HZ x)
    (hY : TwoAvoidance HY Y) (hZ : TwoAvoidance HZ Z) (hYZ : Disjoint Y Z)
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
  rcases disjoint_terminal_pair_opposing F HY HZ x Y Z hu hf hcY hcZ hY hZ hYZ
    Q P hQR hPR (htrace Q hQR) (htrace P hPR) hd with h | h
  · exact hnQ (Finset.mem_filter.mpr ⟨hQR, h.1⟩)
  · exact hnP (Finset.mem_filter.mpr ⟨hPR, h.2⟩)

theorem residual_card_le_27_add_pureY
    (F HY HZ : Finset (Finset α)) (x : α) (Y Z : Finset α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hcY : HasCones F HY x) (hcZ : HasCones F HZ x)
    (hY : TwoAvoidance HY Y) (hZ : TwoAvoidance HZ Z) (hYZ : Disjoint Y Z)
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
    · exact terminal_without_pureY_intersecting
        F HY HZ x Y Z hu hf hcY hcZ hY hZ hYZ htrace
  have hpartition := Finset.card_sdiff_add_card_eq_card
    (pureTransversalMembers_subset (residual F x) HY (Y ∪ Z) Y)
  change (residual F x).card ≤ 27 + TY.card
  change (residual F x \ TY).card + TY.card = (residual F x).card at hpartition
  omega

/-- General terminal separation count, allowing mixed pair traces. -/
theorem terminal_separation_card_bound
    (F HY HZ : Finset (Finset α)) (x : α) (Y Z : Finset α)
    (hu : ∀ Q ∈ F, Q.card = 4) (hf : IsSunflowerFree F 3)
    (hcY : HasCones F HY x) (hcZ : HasCones F HZ x)
    (hY : TwoAvoidance HY Y) (hZ : TwoAvoidance HZ Z) (hYZ : Disjoint Y Z)
    (htrace : ∀ Q ∈ residual F x, TerminalTrace Y Z Q)
    (h27 : H27 α) :
    (residual F x).card ≤ 27 + min
      (pureTransversalMembers (residual F x) HY (Y ∪ Z) Y).card
      (pureTransversalMembers (residual F x) HZ (Y ∪ Z) Z).card := by
  have hboundY := residual_card_le_27_add_pureY
    F HY HZ x Y Z hu hf hcY hcZ hY hZ hYZ htrace h27
  have hswap : ∀ Q ∈ residual F x, TerminalTrace Z Y Q := by
    intro Q hQ
    rcases htrace Q hQ with h | h | h
    · left
      simpa only [Finset.union_comm Z Y] using h
    · right; right
      simpa only [PureTriple, Finset.union_comm Z Y] using h
    · right; left
      simpa only [PureTriple, Finset.union_comm Z Y] using h
  have hboundZ : (residual F x).card ≤ 27 +
      (pureTransversalMembers (residual F x) HZ (Y ∪ Z) Z).card := by
    simpa only [Finset.union_comm Z Y] using
      residual_card_le_27_add_pureY
        F HZ HY x Z Y hu hf hcZ hcY hZ hY hYZ.symm hswap h27
  omega

#print axioms disjoint_union_trace_ge_six
#print axioms residual_intersecting_of_trace_le_two
#print axioms disjoint_terminal_pair_opposing
#print axioms residual_intersecting_of_no_pureY
#print axioms residual_card_le_27_of_trace_le_two
#print axioms residual_card_le_27_of_no_pureY
#print axioms terminal_separation_card_bound

end FrontierTerminal
