import SunflowerLean.Basic
import SunflowerLean.Spread
import Mathlib.Tactic

/-!
# Erdős Problem 20: a conditional constant-scale spread reduction

This file isolates the exact missing interface in the modern spread route.
No new axiom is introduced: `DirectSpreadMatching` is an ordinary proposition
which must be supplied as a theorem argument.
-/

namespace Erdos20BCWConditional

/-- The members of `family` which contain `core`. -/
def upperStar {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (core : Finset α) : Finset (Finset α) :=
  family.filter (fun S => core ⊆ S)

/-- Delete a common core from every member of its upper star. -/
def residualLink {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (core : Finset α) : Finset (Finset α) :=
  (upperStar family core).image (fun S => S \ core)

lemma mem_upperStar_iff {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {core S : Finset α} :
    S ∈ upperStar family core ↔ S ∈ family ∧ core ⊆ S := by
  simp [upperStar]

lemma mem_residualLink_iff {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {core P : Finset α} :
    P ∈ residualLink family core ↔
      ∃ S ∈ family, core ⊆ S ∧ S \ core = P := by
  simp only [residualLink, Finset.mem_image, mem_upperStar_iff]
  aesop

/-- Deleting a fixed subset is injective on sets containing that subset. -/
lemma sdiff_injOn_upperStar {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (core : Finset α) :
    Set.InjOn (fun S : Finset α => S \ core) (upperStar family core) := by
  intro S hS T hT hEq
  have hSc := (mem_upperStar_iff.mp hS).2
  have hTc := (mem_upperStar_iff.mp hT).2
  ext x
  by_cases hx : x ∈ core
  · simp [hSc hx, hTc hx]
  · have hxEq := Finset.ext_iff.mp hEq x
    simpa [hx] using hxEq

lemma card_residualLink {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (core : Finset α) :
    (residualLink family core).card = (upperStar family core).card := by
  exact Finset.card_image_of_injOn (sdiff_injOn_upperStar family core)

/-- The finite universe of cores relevant to a finite family. -/
def support {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) : Finset α :=
  family.biUnion id

def coreCandidates {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) : Finset (Finset α) :=
  (support family).powerset

/-- A core is `q`-dense when its upper-star mass, charged by `q^|core|`,
is at least the mass of the original family. -/
def IsDenseCore {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (q : ℕ) (core : Finset α) : Prop :=
  family.card ≤ (upperStar family core).card * q ^ core.card

noncomputable def denseCores {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (q : ℕ) : Finset (Finset α) :=
  by
    classical
    exact (coreCandidates family).filter (IsDenseCore family q)

lemma empty_mem_denseCores {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (q : ℕ) :
    ∅ ∈ denseCores family q := by
  classical
  simp [denseCores, coreCandidates, support, IsDenseCore, upperStar]

/-- A cardinality-maximal dense core exists because all relevant cores lie in
the finite support of the family. -/
theorem exists_maximal_dense_core {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (q : ℕ) :
    ∃ core ∈ denseCores family q,
      ∀ other ∈ denseCores family q, other.card ≤ core.card := by
  exact Finset.exists_max_image (denseCores family q) Finset.card
    ⟨∅, empty_mem_denseCores family q⟩

lemma filter_residualLink_eq_image_upperStar_union
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (core extra : Finset α)
    (hdis : Disjoint core extra) :
    (residualLink family core).filter (fun P => extra ⊆ P) =
      (upperStar family (core ∪ extra)).image (fun S => S \ core) := by
  ext P
  constructor
  · intro hP
    have hP' := Finset.mem_filter.mp hP
    rcases mem_residualLink_iff.mp hP'.1 with ⟨S, hSF, hcoreS, hSP⟩
    apply Finset.mem_image.mpr
    refine ⟨S, ?_, hSP⟩
    apply mem_upperStar_iff.mpr
    refine ⟨hSF, Finset.union_subset hcoreS ?_⟩
    intro x hx
    have hxP : x ∈ P := hP'.2 hx
    rw [← hSP] at hxP
    exact (Finset.mem_sdiff.mp hxP).1
  · intro hP
    rcases Finset.mem_image.mp hP with ⟨S, hS, hSP⟩
    have hS' := mem_upperStar_iff.mp hS
    apply Finset.mem_filter.mpr
    refine ⟨mem_residualLink_iff.mpr
      ⟨S, hS'.1, Finset.Subset.trans Finset.subset_union_left hS'.2, hSP⟩, ?_⟩
    intro x hx
    rw [← hSP]
    apply Finset.mem_sdiff.mpr
    refine ⟨hS'.2 (Finset.mem_union_right core hx), ?_⟩
    exact fun hxcore => Finset.disjoint_left.mp hdis hxcore hx

lemma card_filter_residualLink
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (core extra : Finset α)
    (hdis : Disjoint core extra) :
    ((residualLink family core).filter (fun P => extra ⊆ P)).card =
      (upperStar family (core ∪ extra)).card := by
  rw [filter_residualLink_eq_image_upperStar_union family core extra hdis]
  apply Finset.card_image_of_injOn
  intro S hS T hT hEq
  apply sdiff_injOn_upperStar family core
  · exact mem_upperStar_iff.mpr
      ⟨(mem_upperStar_iff.mp hS).1,
        Finset.Subset.trans Finset.subset_union_left (mem_upperStar_iff.mp hS).2⟩
  · exact mem_upperStar_iff.mpr
      ⟨(mem_upperStar_iff.mp hT).1,
        Finset.Subset.trans Finset.subset_union_left (mem_upperStar_iff.mp hT).2⟩
  · exact hEq

lemma member_subset_support {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {S : Finset α} (hS : S ∈ family) :
    S ⊆ support family := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨S, hS, hx⟩

/-- A maximal dense core has an absolutely `q`-spread residual link.  This is
the elementary lossless decomposition step; the difficult input is packing a
large spread link at constant `q/p`. -/
theorem maximal_dense_core_residual_isSpread
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (q : ℕ)
    (hfamily : family.Nonempty) (hq : 0 < q)
    (core : Finset α)
    (hcore : core ∈ denseCores family q)
    (hmax : ∀ other ∈ denseCores family q, other.card ≤ core.card) :
    IsRSpread (residualLink family core) q := by
  classical
  have hdense : IsDenseCore family q core := by
    exact (Finset.mem_filter.mp hcore).2
  have hstar : (upperStar family core).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hfamily_pos : 0 < family.card := Finset.card_pos.mpr hfamily
    have hstar_card : (upperStar family core).card = 0 := by simp [h]
    have hzero : family.card ≤ 0 := by
      simpa [IsDenseCore, hstar_card] using hdense
    omega
  refine ⟨hq, ?_, ?_⟩
  · exact Finset.image_nonempty.mpr hstar
  · intro extra
    by_contra hbound
    have hviol : (residualLink family core).card <
        ((residualLink family core).filter (fun P => extra ⊆ P)).card *
          q ^ extra.card := Nat.lt_of_not_ge hbound
    have hextra : extra.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      subst extra
      simp at hviol
    have hfiltered :
        ((residualLink family core).filter (fun P => extra ⊆ P)).Nonempty := by
      apply Finset.card_pos.mp
      by_contra h
      have hz : ((residualLink family core).filter
          (fun P => extra ⊆ P)).card = 0 := Nat.eq_zero_of_not_pos h
      simp [hz] at hviol
    rcases hfiltered with ⟨P, hP⟩
    have hP' := Finset.mem_filter.mp hP
    rcases mem_residualLink_iff.mp hP'.1 with ⟨S, hSF, hcoreS, hSP⟩
    have hdis : Disjoint core extra := by
      rw [Finset.disjoint_left]
      intro x hxcore hxextra
      have hxP : x ∈ P := hP'.2 hxextra
      rw [← hSP] at hxP
      exact (Finset.mem_sdiff.mp hxP).2 hxcore
    have hlocal : (upperStar family core).card <
        (upperStar family (core ∪ extra)).card * q ^ extra.card := by
      simpa [card_residualLink,
        card_filter_residualLink family core extra hdis] using hviol
    have hqpow : 0 < q ^ core.card := pow_pos hq _
    have hcharged :
        (upperStar family core).card * q ^ core.card <
          ((upperStar family (core ∪ extra)).card * q ^ extra.card) *
            q ^ core.card :=
      Nat.mul_lt_mul_of_pos_right hlocal hqpow
    have hcard_union : (core ∪ extra).card = core.card + extra.card :=
      Finset.card_union_of_disjoint hdis
    have hotherDense : IsDenseCore family q (core ∪ extra) := by
      unfold IsDenseCore
      calc
        family.card ≤ (upperStar family core).card * q ^ core.card := hdense
        _ ≤ ((upperStar family (core ∪ extra)).card * q ^ extra.card) *
              q ^ core.card := Nat.le_of_lt hcharged
        _ = (upperStar family (core ∪ extra)).card *
              q ^ (core ∪ extra).card := by
          rw [hcard_union, pow_add]
          ac_rfl
    have hotherCandidate : core ∪ extra ∈ coreCandidates family := by
      apply Finset.mem_powerset.mpr
      exact Finset.union_subset
        (Finset.Subset.trans hcoreS (member_subset_support hSF))
        (Finset.Subset.trans hP'.2
          (Finset.Subset.trans (by
            intro x hx
            rw [← hSP] at hx
            exact (Finset.mem_sdiff.mp hx).1)
            (member_subset_support hSF)))
    have hother : core ∪ extra ∈ denseCores family q := by
      exact Finset.mem_filter.mpr ⟨hotherCandidate, hotherDense⟩
    have hle := hmax (core ∪ extra) hother
    rw [hcard_union] at hle
    have hextra_card : 0 < extra.card := hextra.card_pos
    omega

/-- Exact finite formulation of the still-open constant-scale packing leaf.
It says that every `q`-spread `m`-uniform family larger than `q^m` contains
`p` pairwise-disjoint members. -/
def DirectSpreadMatching (q p : ℕ) : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (petals : Finset (Finset α)) (m : ℕ),
    (∀ P ∈ petals, P.card = m) →
    IsRSpread petals q →
    q ^ m < petals.card →
    ∃ matching : Finset (Finset α),
      matching ⊆ petals ∧
      matching.card = p ∧
      IsPairwiseDisjoint matching

#print axioms sdiff_injOn_upperStar
#print axioms card_residualLink
#print axioms exists_maximal_dense_core
#print axioms card_filter_residualLink
#print axioms maximal_dense_core_residual_isSpread
#print axioms DirectSpreadMatching

end Erdos20BCWConditional
