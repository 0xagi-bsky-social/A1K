import SunflowerLean.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Erdős Problem 20: verified codimension-one star infrastructure

This file isolates a statement-faithful, reusable component of both the classical
Erdős--Rado induction and the shadow/compression route for shifted families.

For an `r`-uniform family, all members extending a fixed `(r-1)`-set form a
sunflower.  Consequently, in a `k`-sunflower-free family, every such extension
star has at most `k-1` members.  This is the local codegree fact used in the
standard shadow double count.

The file deliberately does not state that Problem 20 is solved.
-/

namespace Erdos20Research

/-- An `r`-uniform finite set family. -/
def IsUniform {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r : ℕ) : Prop :=
  ∀ S ∈ family, S.card = r

/-- The members of `family` extending `core`. -/
def extensionStar {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (core : Finset α) : Finset (Finset α) :=
  family.filter (fun S => core ⊆ S)

lemma mem_extensionStar_iff {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {core S : Finset α} :
    S ∈ extensionStar family core ↔ S ∈ family ∧ core ⊆ S := by
  simp [extensionStar]

/-- Two distinct `r`-sets extending the same `(r-1)`-set intersect exactly in it. -/
lemma inter_eq_core_of_codim_one {α : Type*} [DecidableEq α]
    {S T core : Finset α} {r : ℕ}
    (hS : S.card = r) (hT : T.card = r)
    (hcore : core.card + 1 = r)
    (hcoreS : core ⊆ S) (hcoreT : core ⊆ T)
    (hne : S ≠ T) :
    S ∩ T = core := by
  apply Finset.Subset.antisymm
  · intro x hx
    by_contra hxcore
    have hxS : x ∈ S := (Finset.mem_inter.mp hx).1
    have hxT : x ∈ T := (Finset.mem_inter.mp hx).2
    have hinsS : insert x core ⊆ S := by
      simpa [Finset.insert_subset_iff] using And.intro hxS hcoreS
    have hinsT : insert x core ⊆ T := by
      simpa [Finset.insert_subset_iff] using And.intro hxT hcoreT
    have hinscard : (insert x core).card = r := by
      rw [Finset.card_insert_of_notMem hxcore, hcore]
    have hSeq : insert x core = S :=
      Finset.eq_of_subset_of_card_le hinsS (by simpa [hS, hinscard])
    have hTeq : insert x core = T :=
      Finset.eq_of_subset_of_card_le hinsT (by simpa [hT, hinscard])
    exact hne (hSeq.symm.trans hTeq)
  · exact fun _ hx => Finset.mem_inter.mpr ⟨hcoreS hx, hcoreT hx⟩

/-- A codimension-one extension star is a sunflower, with its defining core. -/
theorem extensionStar_isSunflower {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (core : Finset α) (r : ℕ)
    (huniform : IsUniform family r)
    (hcore : core.card + 1 = r) :
    IsSunflower (extensionStar family core) (extensionStar family core).card := by
  refine ⟨rfl, core, ?_⟩
  intro S T hS hT hne
  have hS' := (mem_extensionStar_iff.mp hS)
  have hT' := (mem_extensionStar_iff.mp hT)
  exact inter_eq_core_of_codim_one
    (huniform S hS'.1) (huniform T hT'.1) hcore hS'.2 hT'.2 hne

/-- Every codimension-one extension degree is strictly below the forbidden
sunflower size. -/
theorem extensionStar_card_lt {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (core : Finset α) (r k : ℕ)
    (huniform : IsUniform family r)
    (hfree : IsSunflowerFree family k)
    (hcore : core.card + 1 = r) :
    (extensionStar family core).card < k := by
  by_contra hnot
  have hk : k ≤ (extensionStar family core).card := Nat.le_of_not_gt hnot
  obtain ⟨sub, hsub, hsubcard⟩ := Finset.exists_subset_card_eq hk
  apply hfree sub (Finset.Subset.trans hsub (Finset.filter_subset _ _))
  have hsubuniform : IsUniform sub r := by
    intro S hS
    exact huniform S (Finset.filter_subset _ _ (hsub hS))
  have hsubcore : ∀ S ∈ sub, core ⊆ S := by
    intro S hS
    exact (mem_extensionStar_iff.mp (hsub hS)).2
  refine ⟨hsubcard, core, ?_⟩
  intro S T hS hT hne
  exact inter_eq_core_of_codim_one
    (hsubuniform S hS) (hsubuniform T hT) hcore
    (hsubcore S hS) (hsubcore T hT) hne

/-- Natural-number form of the local codegree bound. -/
theorem extensionStar_card_le_pred {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (core : Finset α) (r k : ℕ)
    (huniform : IsUniform family r)
    (hfree : IsSunflowerFree family k)
    (hcore : core.card + 1 = r) :
    (extensionStar family core).card ≤ k - 1 := by
  have hlt := extensionStar_card_lt family core r k huniform hfree hcore
  omega

/-- The lower shadow, represented as all `(r-1)`-subsets of members. -/
def lowerShadow {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r : ℕ) : Finset (Finset α) :=
  family.biUnion (fun S => S.powersetCard (r - 1))

lemma mem_lowerShadow_iff {α : Type*} [DecidableEq α]
    {family : Finset (Finset α)} {E : Finset α} {r : ℕ} :
    E ∈ lowerShadow family r ↔
      ∃ S ∈ family, E ⊆ S ∧ E.card = r - 1 := by
  simp [lowerShadow, Finset.mem_powersetCard]

/-- Every member of the lower shadow has extension degree at most `k-1`, for
positive uniformity. -/
theorem lowerShadow_extension_degree_le {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (E : Finset α) (r k : ℕ)
    (hr : 1 ≤ r)
    (huniform : IsUniform family r)
    (hfree : IsSunflowerFree family k)
    (hE : E ∈ lowerShadow family r) :
    (extensionStar family E).card ≤ k - 1 := by
  obtain ⟨S, hS, hES, hEcard⟩ := mem_lowerShadow_iff.mp hE
  apply extensionStar_card_le_pred family E r k huniform hfree
  omega

lemma card_filter_eq_sum_ite {β : Type*} [DecidableEq β]
    (s : Finset β) (p : β → Prop) [DecidablePred p] :
    (s.filter p).card = ∑ x ∈ s, if p x then 1 else 0 := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Double-count incidences between a family and its lower shadow. -/
lemma incidence_swap {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r : ℕ) :
    (∑ S ∈ family,
        ((lowerShadow family r).filter (fun E => E ⊆ S)).card) =
      ∑ E ∈ lowerShadow family r, (extensionStar family E).card := by
  simp only [extensionStar]
  simp_rw [card_filter_eq_sum_ite]
  exact Finset.sum_comm

/-- In an `r`-uniform family, the number of member--lower-shadow incidences is
exactly `r * family.card`. -/
lemma incidence_left_count {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r : ℕ)
    (hr : 1 ≤ r) (huniform : IsUniform family r) :
    (∑ S ∈ family,
        ((lowerShadow family r).filter (fun E => E ⊆ S)).card) =
      r * family.card := by
  have hchoose : Nat.choose r (r - 1) = r := by
    have hr' : r - 1 + 1 = r := by omega
    rw [← hr']
    exact Nat.choose_succ_self_right (r - 1)
  calc
    (∑ S ∈ family,
        ((lowerShadow family r).filter (fun E => E ⊆ S)).card) =
        ∑ S ∈ family, (S.powersetCard (r - 1)).card := by
          apply Finset.sum_congr rfl
          intro S hS
          congr 1
          ext E
          constructor
          · intro hE
            have hE' := Finset.mem_filter.mp hE
            rcases mem_lowerShadow_iff.mp hE'.1 with
              ⟨T, hT, hET, hEcard⟩
            exact Finset.mem_powersetCard.mpr
              ⟨hE'.2, hEcard⟩
          · intro hE
            have hE' := Finset.mem_powersetCard.mp hE
            exact Finset.mem_filter.mpr
              ⟨mem_lowerShadow_iff.mpr ⟨S, hS, hE'.1, hE'.2⟩, hE'.1⟩
    _ = ∑ _S ∈ family, r := by
          apply Finset.sum_congr rfl
          intro S hS
          rw [Finset.card_powersetCard, huniform S hS, hchoose]
    _ = r * family.card := by simp [Nat.mul_comm]

/-- Abstract shadow inequality from a uniform extension-degree bound. -/
theorem incidence_inequality {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r k : ℕ)
    (hr : 1 ≤ r)
    (huniform : IsUniform family r)
    (hdegree : ∀ E ∈ lowerShadow family r,
      (extensionStar family E).card ≤ k - 1) :
    r * family.card ≤ (k - 1) * (lowerShadow family r).card := by
  rw [← incidence_left_count family r hr huniform,
    incidence_swap family r]
  calc
    (∑ E ∈ lowerShadow family r, (extensionStar family E).card) ≤
        ∑ _E ∈ lowerShadow family r, (k - 1) := by
          exact Finset.sum_le_sum fun E hE => hdegree E hE
    _ = (k - 1) * (lowerShadow family r).card := by
          simp [Nat.mul_comm]

/-- Verified shadow inequality for a `k`-sunflower-free `r`-uniform family:
`r * |family| ≤ (k-1) * |lowerShadow family r|`.

This is the integer, division-free form of the shadow double count. -/
theorem sunflowerFree_shadow_inequality {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r k : ℕ)
    (hr : 1 ≤ r)
    (huniform : IsUniform family r)
    (hfree : IsSunflowerFree family k) :
    r * family.card ≤ (k - 1) * (lowerShadow family r).card := by
  apply incidence_inequality family r k hr huniform
  intro E hE
  exact lowerShadow_extension_degree_le family E r k hr huniform hfree hE

/-! ## A checked obstruction to the unrestricted shifting bridge removed from v2 -/

/-- The standard family-aware `(i,j)` compression of one set. -/
def ijShiftSet {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i j : α) (S : Finset α) : Finset α :=
  let candidate := insert i (S.erase j)
  if i ∉ S ∧ j ∈ S ∧ candidate ∉ family then candidate else S

/-- Apply an `(i,j)` compression to every member of a finite family. -/
def ijShift {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (i j : α) : Finset (Finset α) :=
  family.image (ijShiftSet family i j)

/-- Stability under every order-decreasing compression on a finite ordinal. -/
def IsFullyShiftedFin {n : ℕ} (family : Finset (Finset (Fin n))) : Prop :=
  ∀ i j : Fin n, i < j → ijShift family i j = family

def shiftCounterexampleOriginalSet : Finset (Fin 4) := {2, 3}

def shiftCounterexampleFinalSet : Finset (Fin 4) := {0, 1}

def shiftCounterexampleStart : Finset (Finset (Fin 4)) :=
  {shiftCounterexampleOriginalSet}

def shiftCounterexampleFinal : Finset (Finset (Fin 4)) :=
  {shiftCounterexampleFinalSet}

/-- Two ordinary compressions take the singleton family `{{2,3}}` to the fully
shifted family `{{0,1}}`, but its final member is not obtained from the original
member by a single replacement `x ↦ 0`.

This finite certificate pinpoints why a final shifted set has no canonical
one-step source in the original family after a sequence of compressions. -/
theorem final_shifted_set_has_no_original_one_step_source :
    ijShift (ijShift shiftCounterexampleStart 0 2) 1 3 =
        shiftCounterexampleFinal ∧
      IsFullyShiftedFin shiftCounterexampleFinal ∧
      ¬ ∃ x : Fin 4,
        shiftCounterexampleFinalSet =
          insert 0 (shiftCounterexampleOriginalSet.erase x) := by
  constructor
  · decide
  constructor
  · rw [IsFullyShiftedFin]
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [ijShift, ijShiftSet, shiftCounterexampleFinal,
        shiftCounterexampleFinalSet]
  · rintro ⟨x, hx⟩
    have hmem : (1 : Fin 4) ∈ shiftCounterexampleFinalSet := by
      decide
    rw [hx] at hmem
    simpa [shiftCounterexampleOriginalSet] using hmem

#print axioms inter_eq_core_of_codim_one
#print axioms extensionStar_isSunflower
#print axioms extensionStar_card_lt
#print axioms extensionStar_card_le_pred
#print axioms lowerShadow_extension_degree_le
#print axioms incidence_swap
#print axioms incidence_left_count
#print axioms incidence_inequality
#print axioms sunflowerFree_shadow_inequality
#print axioms final_shifted_set_has_no_original_one_step_source

end Erdos20Research
