import SunflowerLean.Erdos20Obstructions
import SunflowerLean.Erdos20Critical
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Prod

/-!
# Tensor products of uniform sunflower-free families

The coordinate rigidity argument below proves multiplicativity of finite
lower-bound witnesses. It is a closure theorem, not an upper bound for the
sunflower conjecture. All ground sets in the product are disjoint by type.
-/
namespace Erdos20LocalStructure

/-- The product uses a tagged disjoint union of ground sets. -/
def tensorFamily {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset (Finset α)) (G : Finset (Finset β)) :
    Finset (Finset (α ⊕ β)) :=
  (F ×ˢ G).image (fun pair => pair.1.disjSum pair.2)

theorem mem_tensorFamily_iff {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset (Finset α)) (G : Finset (Finset β)) (S : Finset (α ⊕ β)) :
    S ∈ tensorFamily F G ↔ S.toLeft ∈ F ∧ S.toRight ∈ G := by
  constructor
  · intro h
    obtain ⟨⟨A, B⟩, hAB, rfl⟩ := Finset.mem_image.mp h
    simpa using Finset.mem_product.mp hAB
  · intro h
    exact Finset.mem_image.mpr ⟨(S.toLeft, S.toRight),
      Finset.mem_product.mpr h, Finset.toLeft_disjSum_toRight⟩

theorem card_tensorFamily {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset (Finset α)) (G : Finset (Finset β)) :
    (tensorFamily F G).card = F.card * G.card := by
  rw [tensorFamily, Finset.card_image_of_injective, Finset.card_product]
  intro A B h
  exact Prod.ext (Finset.disjSum_inj.mp h).1 (Finset.disjSum_inj.mp h).2

theorem uniform_tensorFamily {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset (Finset α)) (G : Finset (Finset β)) (r s : ℕ)
    (hF : ∀ A ∈ F, A.card = r) (hG : ∀ B ∈ G, B.card = s) :
    ∀ S ∈ tensorFamily F G, S.card = r + s := by
  intro S hS
  have h := (mem_tensorFamily_iff F G S).mp hS
  rw [← Finset.card_toLeft_add_card_toRight, hF _ h.1, hG _ h.2]

/-- An injective intersection-preserving projection carries a sunflower to a
sunflower of the same size. -/
theorem sunflower_image_of_injective
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (H : Finset (Finset α)) (p : ℕ) (π : Finset α → Finset β)
    (hsun : IsSunflower H p)
    (hinj : Set.InjOn π H)
    (hinter : ∀ A B, π (A ∩ B) = π A ∩ π B) :
    IsSunflower (H.image π) p := by
  obtain ⟨hcard, C, hC⟩ := hsun
  refine ⟨(Finset.card_image_iff.mpr hinj).trans hcard, π C, ?_⟩
  intro A B hA hB hne
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hB
  rw [← hinter, hC S T hS hT (fun h => hne (congrArg π h))]

/-- On a uniform projected sunflower, any collision forces the projection to
be constant. This is the key rigidity fact behind tensor closure. -/
theorem sunflower_projection_injective_or_constant
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (H : Finset (Finset α)) (p r : ℕ) (π : Finset α → Finset β)
    (hsun : IsSunflower H p)
    (huniform : ∀ S ∈ H, (π S).card = r)
    (hinter : ∀ A B, π (A ∩ B) = π A ∩ π B) :
    Set.InjOn π H ∨ ∃ A : Finset β, ∀ S ∈ H, π S = A := by
  classical
  by_cases hinj : Set.InjOn π H
  · exact Or.inl hinj
  · right
    simp only [Set.InjOn] at hinj
    push_neg at hinj
    obtain ⟨S, hS, T, hT, hST, hne⟩ := hinj
    obtain ⟨_, C, hC⟩ := hsun
    have hcore : π C = π S := by
      rw [← hC S T hS hT hne, hinter, hST, Finset.inter_self]
    refine ⟨π S, ?_⟩
    intro U hU
    by_cases hUS : U = S
    · simp [hUS]
    · have hsub : π S ⊆ π U := by
        have hi : π S ∩ π U = π S := by
          rw [← hinter, hC S U hS hU (Ne.symm hUS), hcore]
        exact Finset.inter_eq_left.mp hi
      exact (Finset.eq_of_subset_of_card_le hsub
        (by rw [huniform S hS, huniform U hU])).symm

/-- Sunflower-free witnesses are closed under the disjoint-ground product
when the left factor is uniform. The right factor need not be uniform. -/
theorem sunflowerFree_tensorFamily
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset (Finset α)) (G : Finset (Finset β)) (r p : ℕ)
    (hF : ∀ A ∈ F, A.card = r)
    (hFfree : IsSunflowerFree F p) (hGfree : IsSunflowerFree G p) :
    IsSunflowerFree (tensorFamily F G) p := by
  classical
  intro H hH hsun
  have hleft : ∀ S ∈ H, S.toLeft ∈ F := fun S hS =>
    ((mem_tensorFamily_iff F G S).mp (hH hS)).1
  have hright : ∀ S ∈ H, S.toRight ∈ G := fun S hS =>
    ((mem_tensorFamily_iff F G S).mp (hH hS)).2
  have hleftImage : H.image Finset.toLeft ⊆ F := by
    intro A hA
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hA
    exact hleft S hS
  have hrightImage : H.image Finset.toRight ⊆ G := by
    intro B hB
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hB
    exact hright S hS
  obtain hinj | ⟨A, hconstant⟩ := sunflower_projection_injective_or_constant
    H p r Finset.toLeft hsun (fun S hS => hF _ (hleft S hS))
      (fun S T => Finset.toLeft_inter)
  · exact hFfree _ hleftImage (sunflower_image_of_injective H p Finset.toLeft
      hsun hinj (fun S T => Finset.toLeft_inter))
  · have hinjRight : Set.InjOn (Finset.toRight : Finset (α ⊕ β) → Finset β) H := by
      intro S hS T hT hST
      calc
        S = S.toLeft.disjSum S.toRight := Finset.toLeft_disjSum_toRight.symm
        _ = T.toLeft.disjSum T.toRight := by rw [hconstant S hS, hconstant T hT, hST]
        _ = T := Finset.toLeft_disjSum_toRight
    exact hGfree _ hrightImage (sunflower_image_of_injective H p Finset.toRight
      hsun hinjRight (fun S T => Finset.toRight_inter))

universe u

/-- Existence of a finite uniform sunflower-free witness, with an arbitrary
ambient type in one fixed universe. -/
def UniformFreeWitness (p r N : ℕ) : Prop :=
  ∃ (α : Type u) (_ : DecidableEq α) (F : Finset (Finset α)),
    (∀ S ∈ F, S.card = r) ∧ IsSunflowerFree F p ∧ F.card = N

theorem tensor_witness {p r s M N : ℕ}
    (hF : UniformFreeWitness.{u} p r M)
    (hG : UniformFreeWitness.{u} p s N) :
    UniformFreeWitness.{u} p (r + s) (M * N) := by
  obtain ⟨α, instA, F, huF, hfF, hcF⟩ := hF
  obtain ⟨β, instB, G, huG, hfG, hcG⟩ := hG
  refine ⟨α ⊕ β, inferInstance, tensorFamily F G,
    uniform_tensorFamily F G r s huF huG,
    sunflowerFree_tensorFamily F G r p huF hfF hfG, ?_⟩
  rw [card_tensorFamily, hcF, hcG]

theorem rank_zero_witness {p : ℕ} (hp : 2 ≤ p) :
    UniformFreeWitness.{u} p 0 1 := by
  refine ⟨ULift.{u} Unit, inferInstance, {∅}, ?_, ?_, by simp⟩
  · simp
  · intro H hH hsun
    have hle : H.card ≤ 1 := by simpa using Finset.card_le_card hH
    have heq := hsun.1
    omega

/-- Tensor powers amplify finite witnesses without changing the number of
forbidden petals. -/
theorem tensor_power_witness {p r N : ℕ} (hp : 2 ≤ p)
    (hF : UniformFreeWitness.{u} p r N) (n : ℕ) :
    UniformFreeWitness.{u} p (r * n) (N ^ n) := by
  induction n with
  | zero => simpa using rank_zero_witness hp
  | succ n ih =>
      simpa [Nat.mul_succ, pow_succ] using tensor_witness ih hF

/-- The existing five-cycle certificate yields explicit exponentially large
three-sunflower-free families in every even rank. -/
theorem cycle_five_power_witness (n : ℕ) :
    UniformFreeWitness.{0} 3 (2 * n) (5 ^ n) := by
  apply tensor_power_witness (by decide)
  exact ⟨Fin 5, inferInstance, Erdos20Obstructions.cycleFive,
    Erdos20Obstructions.cycleFive_uniform,
    Erdos20Obstructions.cycleFive_sunflower_free,
    Erdos20Obstructions.cycleFive_card⟩

/-- A fixed-base estimate imposed only above some rank cutoff. -/
def EventualUniformBound (q p : ℕ) : Prop :=
  ∃ R : ℕ, ∀ {α : Type u} [DecidableEq α] (F : Finset (Finset α)) (r : ℕ),
    R ≤ r → (∀ S ∈ F, S.card = r) → IsSunflowerFree F p → F.card ≤ q ^ r

/-- A same-base upper bound valid at all sufficiently large ranks already
holds at every rank: any counterexample would amplify past the cutoff. -/
theorem uniformBound_of_eventual {q p : ℕ} (hp : 2 ≤ p)
    (heventual : EventualUniformBound.{u} q p) :
    Erdos20StrictCore.UniformSunflowerBound.{u} q p := by
  obtain ⟨R, hR⟩ := heventual
  intro α inst F r huniform hfree
  by_contra hnot
  have hlarge : q ^ r < F.card := Nat.lt_of_not_ge hnot
  have hr : 0 < r := by
    by_contra hnonpos
    have hz : r = 0 := by omega
    have hsub : F ⊆ ({∅} : Finset (Finset α)) := by
      intro S hS
      have hScard : S.card = 0 := by simpa [hz] using huniform S hS
      simp [Finset.card_eq_zero.mp hScard]
    have hle : F.card ≤ 1 := by simpa using Finset.card_le_card hsub
    simp [hz] at hlarge
    omega
  obtain ⟨β, instB, G, huG, hfG, hcG⟩ := tensor_power_witness hp
    (show UniformFreeWitness.{u} p r F.card from
      ⟨α, inst, F, huniform, hfree, rfl⟩) (R + 1)
  have hrank : R ≤ r * (R + 1) := by
    have h := Nat.le_mul_of_pos_left (R + 1) hr
    omega
  have hupper := hR G (r * (R + 1)) hrank huG hfG
  rw [hcG, pow_mul] at hupper
  have hlower := Nat.pow_lt_pow_left hlarge (show R + 1 ≠ 0 by omega)
  omega

theorem uniformBound_iff_eventual {q p : ℕ} (hp : 2 ≤ p) :
    Erdos20StrictCore.UniformSunflowerBound.{u} q p ↔ EventualUniformBound.{u} q p := by
  constructor
  · intro h
    exact ⟨0, fun F r _ hu hf => h F r hu hf⟩
  · exact uniformBound_of_eventual hp

/-- A universal exponential estimate with a fixed multiplicative prefactor. -/
def UniformBoundWithPrefactor (q p K : ℕ) : Prop :=
  ∀ {α : Type u} [DecidableEq α] (F : Finset (Finset α)) (r : ℕ),
    (∀ S ∈ F, S.card = r) → IsSunflowerFree F p → F.card ≤ K * q ^ r

/-- Tensor powers absorb every fixed multiplicative prefactor at the same
positive exponential base. The rational comparison is inside Lean. -/
theorem uniformBound_of_prefactor {q p K : ℕ} (hq : 0 < q) (hp : 2 ≤ p)
    (hbound : UniformBoundWithPrefactor.{u} q p K) :
    Erdos20StrictCore.UniformSunflowerBound.{u} q p := by
  intro α inst F r huniform hfree
  by_contra hnot
  have hlarge : q ^ r < F.card := Nat.lt_of_not_ge hnot
  have hqrat : 0 < (q : ℚ) := by exact_mod_cast hq
  have hBpos : 0 < (q : ℚ) ^ r := pow_pos hqrat r
  have hlargeRat : (q : ℚ) ^ r < (F.card : ℚ) := by exact_mod_cast hlarge
  have hratio : 1 < (F.card : ℚ) / (q : ℚ) ^ r := by
    exact (lt_div_iff₀ hBpos).mpr (by simpa using hlargeRat)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (K : ℚ) hratio
  obtain ⟨β, instB, G, huG, hfG, hcG⟩ := tensor_power_witness hp
    (show UniformFreeWitness.{u} p r F.card from
      ⟨α, inst, F, huniform, hfree, rfl⟩) n
  have hupper := hbound G (r * n) huG hfG
  rw [hcG, pow_mul] at hupper
  have hcast : (F.card : ℚ) ^ n ≤ (K : ℚ) * ((q : ℚ) ^ r) ^ n := by
    exact_mod_cast hupper
  have hratle : ((F.card : ℚ) / (q : ℚ) ^ r) ^ n ≤ K := by
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos hBpos n)).mpr hcast
  exact (not_lt_of_ge hratle) hn

theorem uniformBound_iff_exists_prefactor {q p : ℕ} (hq : 0 < q) (hp : 2 ≤ p) :
    Erdos20StrictCore.UniformSunflowerBound.{u} q p ↔
      ∃ K, UniformBoundWithPrefactor.{u} q p K := by
  constructor
  · intro h
    refine ⟨1, ?_⟩
    intro α inst F r hu hf
    simpa using h F r hu hf
  · rintro ⟨K, hK⟩
    exact uniformBound_of_prefactor hq hp hK

/-- Removing both uniformity assumptions makes tensor closure false: each
factor has two sets, but the product contains the three sets ∅,{a},{b}. -/
theorem nonuniform_tensor_failure :
    let F : Finset (Finset (Fin 1)) := {∅, {0}}
    IsSunflowerFree F 3 ∧ ¬ IsSunflowerFree (tensorFamily F F) 3 := by
  dsimp
  constructor
  · intro H hH hsun
    have hle : H.card ≤ 2 := by
      calc
        H.card ≤ ({∅, {0}} : Finset (Finset (Fin 1))).card := Finset.card_le_card hH
        _ = 2 := by decide
    have heq := hsun.1
    omega
  · intro hfree
    let H : Finset (Finset (Fin 1 ⊕ Fin 1)) := {∅, {Sum.inl 0}, {Sum.inr 0}}
    apply hfree H
    · decide
    · refine ⟨by decide, ∅, ?_⟩
      decide

end Erdos20LocalStructure

#print axioms Erdos20LocalStructure.sunflowerFree_tensorFamily
#print axioms Erdos20LocalStructure.tensor_power_witness
#print axioms Erdos20LocalStructure.uniformBound_iff_eventual
#print axioms Erdos20LocalStructure.uniformBound_iff_exists_prefactor
#print axioms Erdos20LocalStructure.nonuniform_tensor_failure
