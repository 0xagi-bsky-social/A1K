import SunflowerLean.Erdos20SpreadPacking
import SunflowerLean.ErdosRadoBound

/-!
# Exact-size normal forms for a least-rank counterexample

A failure of a proposed fixed-base bound has a least failing rank. Truncation
then gives exactly q^r+1 members, while every nonempty link has an absolute
codegree bound from smaller ranks. This is an exact structural reduction, not
a proof that such counterexamples do not exist for a suitable base.
-/
namespace Erdos20Critical

open Erdos20BCWConditional Erdos20StrictCore Erdos20SpreadPacking

universe u

/-- Universal bounds strictly below a specified rank. -/
def LowerRanksBound (q p r : ℕ) : Prop :=
  ∀ {α : Type u} [DecidableEq α] (family : Finset (Finset α)) (m : ℕ),
    m < r → (∀ S ∈ family, S.card = m) → IsSunflowerFree family p →
    family.card ≤ q ^ m

/-- Exact-size free family at a specified rank, with no fixed ambient size. -/
def CriticalFamilyExists (q p r : ℕ) : Prop :=
  ∃ (α : Type u) (_ : DecidableEq α) (family : Finset (Finset α)),
    (∀ S ∈ family, S.card = r) ∧ IsSunflowerFree family p ∧
    family.card = q ^ r + 1

/-- Failure of the fixed-base bound at one rank. -/
def RankCounterexample (q p r : ℕ) : Prop :=
  ∃ (α : Type u) (_ : DecidableEq α) (family : Finset (Finset α)),
    (∀ S ∈ family, S.card = r) ∧ IsSunflowerFree family p ∧
    q ^ r < family.card

/-- Truncate without losing uniformity or sunflower-freeness. -/
theorem exists_exact_size_free_subfamily
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r q p : ℕ)
    (huniform : ∀ S ∈ family, S.card = r)
    (hfree : IsSunflowerFree family p)
    (hlarge : q ^ r < family.card) :
    ∃ critical : Finset (Finset α), critical ⊆ family ∧
      critical.card = q ^ r + 1 ∧
      (∀ S ∈ critical, S.card = r) ∧ IsSunflowerFree critical p := by
  obtain ⟨critical, hsub, hcard⟩ := Finset.exists_subset_card_eq
    (show q ^ r + 1 ≤ family.card by omega)
  refine ⟨critical, hsub, hcard, ?_, ?_⟩
  · intro S hS
    exact huniform S (hsub hS)
  · intro sunflower hsunSub hsun
    exact hfree sunflower (hsunSub.trans hsub) hsun

/-- An exact-size critical family cannot have rank zero. -/
theorem exact_size_rank_pos
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r q : ℕ)
    (huniform : ∀ S ∈ family, S.card = r)
    (hcard : family.card = q ^ r + 1) : 0 < r := by
  by_contra hnot
  have hr : r = 0 := by omega
  have hsub : family ⊆ ({∅} : Finset (Finset α)) := by
    intro S hS
    have hScard : S.card = 0 := by simpa [hr] using huniform S hS
    simpa [Finset.card_eq_zero.mp hScard]
  have hle : family.card ≤ 1 := by simpa using Finset.card_le_card hsub
  simp [hr] at hcard
  omega

/-- Any failure has a least rank and an exact-size representative at that rank. -/
theorem exists_minimal_critical
    {q p : ℕ} (hfailure : ¬ UniformSunflowerBound.{u} q p) :
    ∃ r, 0 < r ∧ LowerRanksBound.{u} q p r ∧
      CriticalFamilyExists.{u} q p r := by
  classical
  have hex : ∃ r, RankCounterexample.{u} q p r := by
    unfold UniformSunflowerBound at hfailure
    push_neg at hfailure
    obtain ⟨α, inst, family, r, huniform, hfree, hlarge⟩ := hfailure
    exact ⟨r, α, inst, family, huniform, hfree, hlarge⟩
  let r := Nat.find hex
  have hlower : LowerRanksBound.{u} q p r := by
    intro α _ family m hm huniform hfree
    by_contra hnot
    have hcounter : RankCounterexample.{u} q p m :=
      ⟨α, inferInstance, family, huniform, hfree, Nat.lt_of_not_ge hnot⟩
    exact Nat.find_min hex hm hcounter
  obtain ⟨α, inst, family, huniform, hfree, hlarge⟩ := Nat.find_spec hex
  obtain ⟨critical, _hsub, hcard, hcuniform, hcfree⟩ :=
    exists_exact_size_free_subfamily family r q p huniform hfree hlarge
  exact ⟨r, exact_size_rank_pos critical r q hcuniform hcard, hlower,
    α, inst, critical, hcuniform, hcfree, hcard⟩

/-- Every nonempty core leaves a lower-rank residual, giving an absolute
codegree ceiling by minimality of the counterexample rank. -/
theorem upperStar_bound_of_lowerRanks
    {α : Type u} [DecidableEq α]
    (family : Finset (Finset α)) (r q p : ℕ)
    (huniform : ∀ S ∈ family, S.card = r)
    (hfree : IsSunflowerFree family p)
    (hlower : LowerRanksBound.{u} q p r)
    (core : Finset α) (hne : core.Nonempty) (hcard : core.card ≤ r) :
    (upperStar family core).card ≤ q ^ (r - core.card) := by
  rw [← card_residualLink]
  apply hlower (residualLink family core) (r - core.card)
  · have hc := hne.card_pos
    omega
  · exact residualLink_uniform huniform
  · exact residualLink_sunflowerFree hfree

/-- Cores larger than the uniform rank have empty upper stars. -/
theorem upperStar_eq_empty_of_rank_lt
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r : ℕ)
    (huniform : ∀ S ∈ family, S.card = r)
    (core : Finset α) (hcard : r < core.card) :
    upperStar family core = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  have hmem := mem_upperStar_iff.mp hS
  have hle := Finset.card_le_card hmem.2
  rw [huniform S hmem.1] at hle
  omega

/-- The exact-size normal form has strict normalized spread, as a consequence
of the stronger absolute link ceilings. -/
theorem exact_size_isStrictSpread
    {α : Type u} [DecidableEq α]
    (family : Finset (Finset α)) (r q p : ℕ)
    (huniform : ∀ S ∈ family, S.card = r)
    (hfree : IsSunflowerFree family p)
    (hlower : LowerRanksBound.{u} q p r)
    (hq : 0 < q) (hcard : family.card = q ^ r + 1) :
    IsStrictRSpread family q := by
  classical
  have hpos : 0 < family.card := by rw [hcard]; omega
  refine ⟨hq, Finset.card_pos.mp hpos, ?_⟩
  intro core hne
  change (upperStar family core).card * q ^ core.card < family.card
  by_cases hc : core.card ≤ r
  · have hbound := upperStar_bound_of_lowerRanks family r q p huniform hfree hlower core hne hc
    calc
      (upperStar family core).card * q ^ core.card ≤
          q ^ (r - core.card) * q ^ core.card := Nat.mul_le_mul_right _ hbound
      _ = q ^ r := by rw [← pow_add, Nat.sub_add_cancel hc]
      _ < family.card := by omega
  · have hempty := upperStar_eq_empty_of_rank_lt family r huniform core (Nat.lt_of_not_ge hc)
    simpa [hempty] using hpos

/-- In the critical normal form the empty core is the only dense core. -/
theorem exact_size_no_nonempty_dense_core
    {α : Type u} [DecidableEq α]
    (family : Finset (Finset α)) (r q p : ℕ)
    (huniform : ∀ S ∈ family, S.card = r)
    (hfree : IsSunflowerFree family p)
    (hlower : LowerRanksBound.{u} q p r)
    (hq : 0 < q) (hcard : family.card = q ^ r + 1)
    (core : Finset α) (hne : core.Nonempty) :
    ¬ IsDenseCore family q core := by
  have hstrict := exact_size_isStrictSpread family r q p huniform hfree hlower hq hcard
  have hlt := hstrict.2.2 core hne
  change (upperStar family core).card * q ^ core.card < family.card at hlt
  intro hdense
  exact Nat.not_le_of_lt hlt hdense

/-- Elementary strict-spread packing excludes all ranks r(p−1) ≤ q. -/
theorem exact_size_rank_product_gt
    {α : Type u} [DecidableEq α]
    (family : Finset (Finset α)) (r q p : ℕ)
    (huniform : ∀ S ∈ family, S.card = r)
    (hfree : IsSunflowerFree family p)
    (hlower : LowerRanksBound.{u} q p r)
    (hq : 0 < q) (hcard : family.card = q ^ r + 1) :
    q < r * (p - 1) := by
  by_contra hnot
  have hr := exact_size_rank_pos family r q huniform hcard
  have hstrict := exact_size_isStrictSpread family r q p huniform hfree hlower hq hcard
  obtain ⟨matching, hsub, hmcard, hdis⟩ := matching_of_strictSpread_low_rank
    family r q p hr huniform hstrict (Nat.le_of_not_gt hnot)
  exact hfree matching hsub (disjoint_is_sunflower matching p hmcard hdis)

/-- The classical factorial bound gives an additional exact rank exclusion. -/
theorem exact_size_factorial_obstruction
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r q p : ℕ)
    (huniform : ∀ S ∈ family, S.card = r)
    (hfree : IsSunflowerFree family p)
    (hcard : family.card = q ^ r + 1) :
    q ^ r < (p - 1) ^ r * r.factorial := by
  have hbound := Erdos20Classical.erdos_rado_factorial_bound family r p huniform hfree
  omega

/-- The exact-size critical family uses at most r(q^r+1) ground elements.
Relabeling this support by a finite ordinal is not asserted by this theorem. -/
theorem exact_size_support_card_bound
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r q : ℕ)
    (huniform : ∀ S ∈ family, S.card = r)
    (hcard : family.card = q ^ r + 1) :
    (support family).card ≤ r * (q ^ r + 1) := by
  have hbound : (family.biUnion id).card ≤ family.card * r :=
    Finset.card_biUnion_le_card_mul family id r (fun S hS => le_of_eq (huniform S hS))
  simpa [support, hcard, Nat.mul_comm] using hbound

#print axioms exact_size_support_card_bound

#print axioms exists_exact_size_free_subfamily
#print axioms exact_size_rank_pos
#print axioms exists_minimal_critical
#print axioms upperStar_bound_of_lowerRanks
#print axioms upperStar_eq_empty_of_rank_lt
#print axioms exact_size_isStrictSpread
#print axioms exact_size_no_nonempty_dense_core
#print axioms exact_size_rank_product_gt
#print axioms exact_size_factorial_obstruction

end Erdos20Critical
