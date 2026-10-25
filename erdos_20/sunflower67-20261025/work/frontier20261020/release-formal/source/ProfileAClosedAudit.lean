import ProfileAClosed
import Lean

open Lean Elab Command

private def auditRoot (target : Name) : CommandElabM Unit := do
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
  logInfo m!"PROFILE_A_CLOSED_AXIOM_AUDIT {receipt.compress}"

syntax (name := profileAClosedAudit) "#profile_a_closed_audit " ident : command
elab_rules : command
  | `(#profile_a_closed_audit $target:ident) => auditRoot target.getId

#profile_a_closed_audit FrontierGenericHeavyExtensions.extensions_card_two
#profile_a_closed_audit FrontierGenericHeavyExtensions.heavy_extensions_common_point
#profile_a_closed_audit FrontierGenericHeavyExtensions.heavy_design_keys_card_le_five
#profile_a_closed_audit FrontierCompletionMass.card_le_degree_sum_of_meeting
#profile_a_closed_audit FrontierCompletionMass.degree_sum_eq_card_of_singleton_intersection
#profile_a_closed_audit FrontierProfileAConcentrated.tails_card_le_ten
#profile_a_closed_audit FrontierProfileAConcentrated.completion_mem_tails
#profile_a_closed_audit FrontierProfileAConcentrated.completion_meets_extensions
#profile_a_closed_audit FrontierProfileAConcentrated.key_heavy
#profile_a_closed_audit FrontierProfileAConcentrated.concentrated_impossible
#profile_a_closed_audit FrontierProfileAClosed.residual_profile_a_impossible
#profile_a_closed_audit FrontierProfileAClosed.no_profile_a_of_intersecting_twenty_seven

#profile_a_closed_audit FrontierProfileAClosed.rank_four_upper_eighty_of_intersecting_and_no_profile_b

#print FrontierProfileAClosed.no_profile_a_of_intersecting_twenty_seven
