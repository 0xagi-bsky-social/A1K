import TwoHighEighty
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

#profile_a_bridge_audit FrontierTwoStarBridge.two_star_partition
#profile_a_bridge_audit FrontierTwoStarBridge.two_star_degree_partition
#profile_a_bridge_audit FrontierTwoStarBridge.high_pair_codegree
#profile_a_bridge_audit FrontierTwoStarBridge.center_outside_link
#profile_a_bridge_audit FrontierTwoStarBridge.residual_degree_bounds
#profile_a_bridge_audit FrontierTwoHighEighty.two_independent_high_card_le_eighty
#profile_a_bridge_audit FrontierTwoHighEighty.degree_twenty_mem_high
#profile_a_bridge_audit FrontierTwoHighEighty.exactly_two_high_card_le_eighty
#profile_a_bridge_audit FrontierTwoHighEighty.profile_b_not_realizable
#profile_a_bridge_audit FrontierTwoHighEighty.independent_twenty_stars_card_le_eighty
#print FrontierTwoHighEighty.independent_twenty_stars_card_le_eighty
