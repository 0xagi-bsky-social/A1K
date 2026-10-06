import SunflowerLean.Erdos20V12Nineteen
import Lean

namespace Erdos20V12AuditExtension
open Erdos20BCWConditional Erdos20Incidence Erdos20V12Nineteen
open Erdos20V8Intersecting Erdos20ExtremalTransversals Erdos20RankThreeEven

theorem nineteen_max_degree_five_transversal_ge_six
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card=3) (hf : IsSunflowerFree F 3) (hc : F.card=19)
    (hd : ∀ x, (F.filter (fun S => x ∈ S)).card≤5)
    (C : Finset α) (hhit : ∀ S ∈ F, (S ∩ C).Nonempty) : 6 ≤ C.card := by
  classical
  obtain ⟨H,K,hF,hHc,hKc,hdis,hHi,hKi⟩ := nineteen_max_degree_five_decomposition F hu hf hc hd
  have hHF : H ⊆ F := by rw [hF]; exact Finset.subset_union_left
  have hKF : K ⊆ F := by rw [hF]; exact Finset.subset_union_right
  have hHf : IsSunflowerFree H 3 := fun G hG hg => hf G (hG.trans hHF) hg
  have hKf : IsSunflowerFree K 3 := fun G hG hg => hf G (hG.trans hKF) hg
  have hH := intersecting_nine_transversal_card_ge_three H (C ∩ support H)
    (fun S hS => hu S (hHF hS)) hHf hHi (by omega)
    (transversal_restrict_support F H C hHF hhit)
  have hK := intersecting_nine_transversal_card_ge_three K (C ∩ support K)
    (fun S hS => hu S (hKF hS)) hKf hKi (by omega)
    (transversal_restrict_support F K C hKF hhit)
  have hCd : Disjoint (C ∩ support H) (C ∩ support K) :=
    hdis.mono Finset.inter_subset_right Finset.inter_subset_right
  have hsub : (C ∩ support H) ∪ (C ∩ support K) ⊆ C :=
    Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hCd] at hcard
  omega

theorem nineteen_transversal_five_has_degree_six
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card=3) (hf : IsSunflowerFree F 3) (hc : F.card=19)
    (C : Finset α) (hC : C.card≤5) (hhit : ∀ S ∈ F, (S ∩ C).Nonempty) :
    ∃ x, (F.filter (fun S => x ∈ S)).card=6 := by
  by_contra hn
  push_neg at hn
  have hd : ∀ x, (F.filter (fun S => x ∈ S)).card≤5 := by
    intro x
    have hb := rank_three_degree_le_six F hu hf x
    have he := hn x
    omega
  have h := nineteen_max_degree_five_transversal_ge_six F hu hf hc hd C hhit
  omega
end Erdos20V12AuditExtension

namespace Erdos20AxiomAudit
open Lean Elab Command

private def auditRoot (target : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.find? target
    | throwError "ERDOS20_AUDIT_MISSING_ROOT: {target}"
  match info with
  | .thmInfo _ => pure ()
  | _ => throwError "ERDOS20_AUDIT_NOT_THEOREM: {target}"
  unless ← liftTermElabM (Lean.Meta.isProp info.type) do
    throwError "ERDOS20_AUDIT_NOT_PROP: {target}"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms target
  let unexpected := axioms.filter fun name => !allowed.contains name
  unless unexpected.isEmpty do
    throwError "ERDOS20_AUDIT_DISALLOWED: root={target}; unexpected={unexpected.toList}"
  let names := (axioms.map Name.toString).qsort (· < ·)
  let receipt := Json.mkObj [
    ("root", Json.str target.toString),
    ("axioms", Json.arr (names.map Json.str)),
    ("status", Json.str "pass")]
  logInfo m!"ERDOS20_AXIOM_AUDIT {receipt.compress}"

syntax (name := erdos20Audit) "#erdos20_audit " ident : command
elab_rules : command
  | `(#erdos20_audit $target:ident) => auditRoot target.getId
end Erdos20AxiomAudit


#erdos20_audit Erdos20V12AuditExtension.nineteen_max_degree_five_transversal_ge_six
#erdos20_audit Erdos20V12AuditExtension.nineteen_transversal_five_has_degree_six
