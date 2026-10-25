import SunflowerLean.Erdos20RankThreeEven
import SunflowerLean.Erdos20FiniteReduction

/-! Compress the remaining sharp triple-bound question to fifteen points. -/
universe u
namespace Erdos20TripleReduction
open Erdos20BCWConditional Erdos20Incidence Erdos20RankThreeEven
open Erdos20FiniteReduction

/-- A twenty-one-member candidate has point degrees between four and six. -/
theorem twenty_one_degree_window {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S ∈ F, S.card = 3)
    (hf : IsSunflowerFree F 3) (hc : F.card = 21)
    (x : α) (hx : x ∈ support F) :
    4 ≤ (F.filter (fun S => x ∈ S)).card ∧
      (F.filter (fun S => x ∈ S)).card ≤ 6 := by
  obtain ⟨R, hR, hxR⟩ := Finset.mem_biUnion.mp hx
  have hlo := rank_three_card_le_degree_add_seventeen F R x hR hxR hu hf
  have hhi := rank_three_degree_le_six F hu hf x
  omega

/-- The total number of incidences is sixty-three. -/
theorem twenty_one_incidence {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S ∈ F, S.card = 3)
    (hc : F.card = 21) :
    (∑ x ∈ support F, (F.filter (fun S => x ∈ S)).card) = 63 := by
  rw [← incidence_sum_eq]
  calc
    _ = ∑ _S ∈ F, 3 := Finset.sum_congr rfl (fun S hS => by
      rw [Finset.inter_eq_left.mpr (member_subset_support hS), hu S hS])
    _ = 63 := by simp [hc]

/-- Only eleven through fifteen supported points are possible. -/
theorem twenty_one_support_window {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S ∈ F, S.card = 3)
    (hf : IsSunflowerFree F 3) (hc : F.card = 21) :
    11 ≤ (support F).card ∧ (support F).card ≤ 15 := by
  have hsum := twenty_one_incidence F hu hc
  have hlo : (support F).card * 4 ≤ 63 := by
    calc
      _ = ∑ _x ∈ support F, 4 := by simp
      _ ≤ ∑ x ∈ support F, (F.filter (fun S => x ∈ S)).card :=
        Finset.sum_le_sum (fun x hx => (twenty_one_degree_window F hu hf hc x hx).1)
      _ = 63 := hsum
  have hhi : 63 ≤ (support F).card * 6 := by
    calc
      _ = ∑ x ∈ support F, (F.filter (fun S => x ∈ S)).card := hsum.symm
      _ ≤ ∑ _x ∈ support F, 6 :=
        Finset.sum_le_sum (fun x hx => (twenty_one_degree_window F hu hf hc x hx).2)
      _ = _ := by simp
  omega

/-- The sharply reduced finite obstruction predicate. -/
def TwentyOneOnFifteen : Prop :=
  ∃ F : Finset (Finset (Fin 15)),
    (∀ S ∈ F, S.card = 3) ∧ IsSunflowerFree F 3 ∧ F.card = 21

/-- Any failure of the upper bound twenty produces this finite obstruction. -/
theorem twenty_one_on_fifteen_of_counterexample {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S ∈ F, S.card = 3)
    (hf : IsSunflowerFree F 3) (hlarge : 20 < F.card) : TwentyOneOnFifteen := by
  obtain ⟨H, hHF, hcard⟩ := Finset.exists_subset_card_eq (show 21 ≤ F.card by omega)
  have huH : ∀ S ∈ H, S.card = 3 := fun S hS => hu S (hHF hS)
  have hfH : IsSunflowerFree H 3 := fun T hT hsun => hf T (hT.trans hHF) hsun
  obtain ⟨K, hcK, huK, hfK⟩ := exists_fin_relabel H 15 3 3
    (twenty_one_support_window H huH hfH hcard).2 huH hfH
  exact ⟨K, huK, hfK, hcK.trans hcard⟩

/-- The target upper bound at rank three, with arbitrary ambient types. -/
def TripleBoundTwenty : Prop :=
  ∀ {α : Type u} [DecidableEq α] (F : Finset (Finset α)),
    (∀ S ∈ F, S.card = 3) → IsSunflowerFree F 3 → F.card ≤ 20

/-- The finite test is equivalent to the literal sharp universal upper bound.
This is a reduction, not a proof that the finite obstruction is absent. -/
theorem triple_bound_twenty_iff :
    TripleBoundTwenty.{u} ↔ ¬ TwentyOneOnFifteen := by
  constructor
  · intro hbound hfinite
    obtain ⟨F, hu, hf, hc⟩ := hfinite
    let e : Fin 15 ↪ ULift.{u} (Fin 15) := Equiv.ulift.symm.toEmbedding
    have hb := hbound (mapFamily e F) (uniform_mapFamily e F 3 hu)
      ((isSunflowerFree_mapFamily_iff e F 3).mpr hf)
    rw [card_mapFamily, hc] at hb
    omega
  · intro hn α _ F hu hf
    by_contra hb
    exact hn (twenty_one_on_fifteen_of_counterexample F hu hf (by omega))

instance twentyOneOnFifteenDecidable : Decidable TwentyOneOnFifteen := by
  unfold TwentyOneOnFifteen
  infer_instance

/-- The computable Boolean has not been exhaustively evaluated. -/
def sharpTripleCheck : Bool := decide TwentyOneOnFifteen

theorem sharpTripleCheck_eq_true_iff : sharpTripleCheck = true ↔ TwentyOneOnFifteen := by
  simp [sharpTripleCheck]

theorem triple_bound_twenty_iff_check_false :
    TripleBoundTwenty.{u} ↔ sharpTripleCheck = false := by
  rw [triple_bound_twenty_iff]
  simp [sharpTripleCheck]

/-- Uniform exact-size candidate domain before checking sunflower-freeness. -/
def sharpCandidates : Finset (Finset (Finset (Fin 15))) :=
  ((Finset.univ : Finset (Fin 15)).powersetCard 3).powersetCard 21

theorem sharpCandidates_card : sharpCandidates.card = Nat.choose 455 21 := by
  simp only [sharpCandidates, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  congr 1

end Erdos20TripleReduction
