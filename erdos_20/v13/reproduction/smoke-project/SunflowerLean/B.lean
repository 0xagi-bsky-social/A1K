import SunflowerLean.A
namespace V13ReplaySmoke
theorem arithmetic : (2 : Nat)+2=4 := by decide
end V13ReplaySmoke
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
#erdos20_audit V13ReplaySmoke.checked
#erdos20_audit V13ReplaySmoke.arithmetic
