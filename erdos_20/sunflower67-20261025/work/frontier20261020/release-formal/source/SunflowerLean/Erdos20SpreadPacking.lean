import SunflowerLean.Erdos20StrictCore
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Elementary packing from strict singleton-degree bounds.
This closes a rank-dependent leaf, not the constant-base sunflower conjecture. -/
namespace Erdos20SpreadPacking

universe u

/-- A transversal meets every member of a finite family. -/
def IsTransversal {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (cover : Finset α) : Prop :=
  ∀ S ∈ family, ∃ x ∈ cover, x ∈ S

/-- Strict singleton spread forces every transversal to have more than q points. -/
theorem strict_singleton_transversal_card_gt
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (cover : Finset α) (q : ℕ)
    (hne : family.Nonempty)
    (hdegree : ∀ x : α, (family.filter (fun S => x ∈ S)).card * q < family.card)
    (hcover : IsTransversal family cover) :
    q < cover.card := by
  classical
  have hcne : cover.Nonempty := by
    obtain ⟨S, hS⟩ := hne
    obtain ⟨x, hx, _⟩ := hcover S hS
    exact ⟨x, hx⟩
  have hsub : family ⊆ cover.biUnion (fun x => family.filter (fun S => x ∈ S)) := by
    intro S hS
    obtain ⟨x, hx, hxS⟩ := hcover S hS
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr ⟨hS, hxS⟩⟩
  have hcount : family.card ≤ ∑ x ∈ cover, (family.filter (fun S => x ∈ S)).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hstrict : (∑ x ∈ cover, (family.filter (fun S => x ∈ S)).card) * q <
      cover.card * family.card := by
    rw [Finset.sum_mul]
    calc
      (∑ x ∈ cover, (family.filter (fun S => x ∈ S)).card * q) <
          ∑ _x ∈ cover, family.card :=
        Finset.sum_lt_sum_of_nonempty hcne (fun x _ => hdegree x)
      _ = cover.card * family.card := by simp
  have hprod : family.card * q < cover.card * family.card :=
    lt_of_le_of_lt (Nat.mul_le_mul_right q hcount) hstrict
  nlinarith

/-- A cardinality-maximal matching exists among the subfamilies. -/
theorem exists_maximum_matching
    {α : Type*} [DecidableEq α] (family : Finset (Finset α)) :
    ∃ matching : Finset (Finset α), matching ⊆ family ∧ IsPairwiseDisjoint matching ∧
      ∀ other : Finset (Finset α), other ⊆ family → IsPairwiseDisjoint other →
        other.card ≤ matching.card := by
  classical
  let candidates := family.powerset.filter IsPairwiseDisjoint
  have hempty : ∅ ∈ candidates := by
    simp [candidates, IsPairwiseDisjoint]
  obtain ⟨matching, hmatch, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card ⟨∅, hempty⟩
  have hmem := Finset.mem_filter.mp hmatch
  refine ⟨matching, Finset.mem_powerset.mp hmem.1, hmem.2, ?_⟩
  intro other hsub hdis
  exact hmax other (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hdis⟩)

/-- The union of a maximum matching covers every nonempty member. -/
theorem maximum_matching_union_transversal
    {α : Type*} [DecidableEq α]
    (family matching : Finset (Finset α))
    (hdis : IsPairwiseDisjoint matching)
    (hnonempty : ∀ S ∈ family, S.Nonempty)
    (hsub : matching ⊆ family)
    (hmax : ∀ other : Finset (Finset α), other ⊆ family → IsPairwiseDisjoint other →
      other.card ≤ matching.card) :
    IsTransversal family (matching.biUnion id) := by
  classical
  intro S hS
  by_contra hmiss
  have hnone : ∀ T ∈ matching, S ∩ T = ∅ := by
    intro T hT
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx' := Finset.mem_inter.mp hx
    exact hmiss ⟨x, Finset.mem_biUnion.mpr ⟨T, hT, hx'.2⟩, hx'.1⟩
  have hnot : S ∉ matching := by
    intro hm
    obtain ⟨x, hx⟩ := hnonempty S hS
    exact hmiss ⟨x, Finset.mem_biUnion.mpr ⟨S, hm, hx⟩, hx⟩
  have hins : IsPairwiseDisjoint (insert S matching) := by
    intro A B hA hB hne
    rcases Finset.mem_insert.mp hA with hAS | hAm
    · subst A
      rcases Finset.mem_insert.mp hB with hBS | hBm
      · exact False.elim (hne hBS.symm)
      · exact hnone B hBm
    · rcases Finset.mem_insert.mp hB with hBS | hBm
      · subst B
        rw [Finset.inter_comm]
        exact hnone A hAm
      · exact hdis A B hAm hBm hne
  have hh := hmax (insert S matching) (Finset.insert_subset_iff.mpr ⟨hS, hsub⟩) hins
  rw [Finset.card_insert_of_notMem hnot] at hh
  omega

/-- Every maximum matching has size ν with q < mν under strict singleton spread. -/
theorem maximum_matching_rank_lower_bound
    {α : Type*} [DecidableEq α]
    (family matching : Finset (Finset α)) (m q : ℕ)
    (hne : family.Nonempty) (hm : 0 < m)
    (huniform : ∀ S ∈ family, S.card = m)
    (hdegree : ∀ x : α, (family.filter (fun S => x ∈ S)).card * q < family.card)
    (hsub : matching ⊆ family) (hdis : IsPairwiseDisjoint matching)
    (hmax : ∀ other : Finset (Finset α), other ⊆ family → IsPairwiseDisjoint other →
      other.card ≤ matching.card) :
    q < m * matching.card := by
  have hcover := maximum_matching_union_transversal family matching hdis
    (fun S hS => Finset.card_pos.mp (by rw [huniform S hS]; exact hm)) hsub hmax
  have hgt := strict_singleton_transversal_card_gt family (matching.biUnion id) q hne hdegree hcover
  have hcard : (matching.biUnion id).card ≤ m * matching.card := by
    calc
      (matching.biUnion id).card ≤ ∑ S ∈ matching, S.card := Finset.card_biUnion_le
      _ = ∑ _S ∈ matching, m := by
        apply Finset.sum_congr rfl
        intro S hS
        exact huniform S (hsub hS)
      _ = m * matching.card := by simp [Nat.mul_comm]
  exact lt_of_lt_of_le hgt hcard

/-- Strict singleton spread packs p disjoint members when m(p−1) ≤ q.
Positive rank is explicit; rank zero admits the exceptional singleton {∅}. -/
theorem matching_of_strict_singleton_spread
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (m q p : ℕ)
    (hne : family.Nonempty) (hm : 0 < m)
    (huniform : ∀ S ∈ family, S.card = m)
    (hdegree : ∀ x : α, (family.filter (fun S => x ∈ S)).card * q < family.card)
    (hthreshold : m * (p - 1) ≤ q) :
    ∃ matching : Finset (Finset α), matching ⊆ family ∧
      matching.card = p ∧ IsPairwiseDisjoint matching := by
  obtain ⟨M, hMsub, hMdis, hMmax⟩ := exists_maximum_matching family
  have hbound := maximum_matching_rank_lower_bound family M m q hne hm huniform
    hdegree hMsub hMdis hMmax
  have hsize : p ≤ M.card := by
    by_contra hh
    have hle : M.card ≤ p - 1 := by omega
    have := Nat.mul_le_mul_left m hle
    omega
  obtain ⟨matching, hsub, hcard⟩ := Finset.exists_subset_card_eq hsize
  refine ⟨matching, hsub.trans hMsub, hcard, ?_⟩
  intro S T hS hT hne
  exact hMdis S T (hsub hS) (hsub hT) hne

/-- Bridge the full strict-spread definition to the elementary packing theorem. -/
theorem matching_of_strictSpread_low_rank
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (m q p : ℕ)
    (hm : 0 < m) (huniform : ∀ S ∈ family, S.card = m)
    (hspread : Erdos20StrictCore.IsStrictRSpread family q)
    (hthreshold : m * (p - 1) ≤ q) :
    ∃ matching : Finset (Finset α), matching ⊆ family ∧
      matching.card = p ∧ IsPairwiseDisjoint matching := by
  apply matching_of_strict_singleton_spread family m q p hspread.2.1 hm huniform
  · intro x
    simpa using hspread.2.2 {x} (Finset.singleton_nonempty x)
  · exact hthreshold

/-- An explicit integer lower bound: floor(q/m)+1 disjoint members. -/
theorem matching_of_strictSpread_floor_bound
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (m q : ℕ)
    (hm : 0 < m) (huniform : ∀ S ∈ family, S.card = m)
    (hspread : Erdos20StrictCore.IsStrictRSpread family q) :
    ∃ matching : Finset (Finset α), matching ⊆ family ∧
      matching.card = q / m + 1 ∧ IsPairwiseDisjoint matching := by
  apply matching_of_strictSpread_low_rank family m q (q / m + 1) hm huniform hspread
  simpa [Nat.mul_comm] using Nat.div_mul_le_self q m

/-- The exact remaining strict-spread sunflower problem after low ranks are closed. -/
def StrictSpreadSunflowerTail (q p : ℕ) : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (m : ℕ),
    (∀ S ∈ family, S.card = m) → 0 < m →
    Erdos20StrictCore.IsStrictRSpread family q → q < m * (p - 1) →
    ∃ sunflower : Finset (Finset α), sunflower ⊆ family ∧ IsSunflower sunflower p

/-- Removing all closed low-rank leaves preserves the exact fixed-base conjecture. -/
theorem strictSpreadSunflowerTail_iff_uniformBound
    {q p : ℕ} (hq : 0 < q) :
    StrictSpreadSunflowerTail.{u} q p ↔ Erdos20StrictCore.UniformSunflowerBound.{u} q p := by
  constructor
  · intro htail
    apply Erdos20StrictCore.uniformBound_of_strictSpreadSunflower hq
    intro α _ family m huniform hm hstrict
    by_cases hlow : m * (p - 1) ≤ q
    · obtain ⟨matching, hsub, hcard, hdis⟩ :=
        matching_of_strictSpread_low_rank family m q p hm huniform hstrict hlow
      exact ⟨matching, hsub, disjoint_is_sunflower matching p hcard hdis⟩
    · exact htail family m huniform hm hstrict (Nat.lt_of_not_ge hlow)
  · intro hbound α _ family m huniform hm hstrict _htail
    exact Erdos20StrictCore.strictSpreadSunflower_of_uniformBound hbound
      family m huniform hm hstrict

#print axioms matching_of_strictSpread_floor_bound
#print axioms strictSpreadSunflowerTail_iff_uniformBound

#print axioms strict_singleton_transversal_card_gt
#print axioms maximum_matching_rank_lower_bound
#print axioms matching_of_strict_singleton_spread
#print axioms matching_of_strictSpread_low_rank
end Erdos20SpreadPacking
