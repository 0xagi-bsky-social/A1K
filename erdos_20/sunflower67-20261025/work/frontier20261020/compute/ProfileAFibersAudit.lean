import ProfileAFibers
import Lean

open Lean Elab Command

private def auditProfileABridgeRoot (target : Name) : CommandElabM Unit := do
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
  let receipt := Json.mkObj [("root",Json.str target.toString),
    ("axioms",Json.arr (names.map Json.str)), ("status",Json.str "pass")]
  logInfo m!"PROFILE_A_BRIDGE_AXIOM_AUDIT {receipt.compress}"

syntax (name := profileABridgeAudit) "#profile_a_bridge_audit " ident : command
elab_rules : command
  | `(#profile_a_bridge_audit $target:ident) => auditProfileABridgeRoot target.getId

#profile_a_bridge_audit FrontierProfileAFibers.row_key_card_two
#profile_a_bridge_audit FrontierProfileAFibers.key_card_two
#profile_a_bridge_audit FrontierProfileAFibers.fiber_card_le_four
#profile_a_bridge_audit FrontierProfileAFibers.rows_card_le_four_mul_keys
