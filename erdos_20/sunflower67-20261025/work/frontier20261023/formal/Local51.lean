import Lean

/-
Pure natural-number arithmetic. Every bound and implication below is a premise.
This file does not prove that geometric or set-family data satisfy those premises.
The abbreviations used informally are d₁ = 5 + a + b + e + s and
 d₂ = 5 + a + c + e + t; their expressions are written literally in the theorem.
-/
namespace FrontierLocal51

set_option maxHeartbeats 400000

/-- The conditional local arithmetic bound; no geometric hypotheses are discharged here. -/
theorem local_weight_le_51
    (a b c e s t : Nat)
    (ha : a ≤ 3) (hb : b ≤ 3) (hc : c ≤ 3) (he : e ≤ 1)
    (hs : s ≤ 10) (ht : t ≤ 10)
    (hd₁ : 5 + a + b + e + s ≤ 20)
    (hd₂ : 5 + a + c + e + t ≤ 20)
    (hsmall₁ : s ≤ 7 → 5 + a + b + e + s ≤ 17)
    (hsmall₂ : t ≤ 7 → 5 + a + c + e + t ≤ 17)
    (hlarge₁ : 8 ≤ s → a ≤ 2 ∧ b ≤ 2)
    (hlarge₂ : 8 ≤ t → a ≤ 2 ∧ c ≤ 2)
    (hboth : 8 ≤ s ∧ 8 ≤ t → e = 0 ∧ a ≤ 1)
    (hmax : (5 + a + b + e + s = 20 ∨
      5 + a + c + e + t = 20) → a = 2 ∧ e = 1) :
    3 * a + 2 * b + 2 * c + 3 * e + 2 * s + 2 * t ≤ 51 := by
  by_cases hs₇ : s ≤ 7
  · have h₁ := hsmall₁ hs₇
    by_cases ht₇ : t ≤ 7
    · have h₂ := hsmall₂ ht₇
      omega
    · have ht₈ : 8 ≤ t := by omega
      obtain ⟨ha₂, hc₂⟩ := hlarge₂ ht₈
      by_cases hd₂₂₀ : 5 + a + c + e + t = 20
      · obtain ⟨haeq, heeq⟩ := hmax (Or.inr hd₂₂₀)
        omega
      · by_cases hd₂₁₉ : 5 + a + c + e + t = 19 <;> omega
  · have hs₈ : 8 ≤ s := by omega
    obtain ⟨ha₂, hb₂⟩ := hlarge₁ hs₈
    by_cases ht₇ : t ≤ 7
    · have h₂ := hsmall₂ ht₇
      by_cases hd₁₂₀ : 5 + a + b + e + s = 20
      · obtain ⟨haeq, heeq⟩ := hmax (Or.inl hd₁₂₀)
        omega
      · by_cases hd₁₁₉ : 5 + a + b + e + s = 19 <;> omega
    · have ht₈ : 8 ≤ t := by omega
      obtain ⟨_, hc₂⟩ := hlarge₂ ht₈
      obtain ⟨heeq, ha₁⟩ := hboth ⟨hs₈, ht₈⟩
      omega

end FrontierLocal51

#check FrontierLocal51.local_weight_le_51
#print axioms FrontierLocal51.local_weight_le_51

open Lean Elab Command

/- Fail closed if the named arithmetic theorem is missing or uses an unapproved axiom. -/
run_cmd do
  let target := ``FrontierLocal51.local_weight_le_51
  let env ← getEnv
  let some info := env.find? target
    | throwError "MISSING_ROOT: {target}"
  match info with
  | .thmInfo _ => pure ()
  | _ => throwError "NOT_THEOREM: {target}"
  unless ← liftTermElabM (Lean.Meta.isProp info.type) do
    throwError "NOT_PROP: {target}"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms target
  let unexpected := axioms.filter fun name => !allowed.contains name
  unless unexpected.isEmpty do
    throwError "DISALLOWED: root={target}; unexpected={unexpected.toList}"
  let names := (axioms.map Name.toString).qsort (· < ·)
  let receipt := Json.mkObj [("root", Json.str target.toString),
    ("axioms", Json.arr (names.map Json.str)), ("status", Json.str "pass")]
  logInfo m!"LOCAL51_AXIOM_AUDIT {receipt.compress}"
