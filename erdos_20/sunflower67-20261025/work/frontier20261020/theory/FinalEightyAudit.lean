import FinalEighty
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
  logInfo m!"FINAL_EIGHTY_AXIOM_AUDIT {receipt.compress}"

syntax (name := finalEightyAudit) "#final_eighty_audit " ident : command
elab_rules : command
  | `(#final_eighty_audit $target:ident) => auditRoot target.getId

#final_eighty_audit FrontierTwoHighIncidence.common_trace_card_ge_two
#final_eighty_audit FrontierTwoHighIncidence.two_large_traces_incidence_bound
#final_eighty_audit FrontierTwoHighIncidence.two_large_supports_card_le_forty
#final_eighty_audit FrontierProfileAClosed.no_profile_a_of_intersecting_twenty_seven
#final_eighty_audit FrontierTwoHighEighty.two_independent_high_card_le_eighty
#final_eighty_audit FrontierTwoHighEighty.profile_b_not_realizable
#final_eighty_audit FrontierFinalEighty.rank_four_upper_eighty_of_intersecting_twenty_seven
#final_eighty_audit FrontierFinalEighty.literal_intersecting_twenty_seven_implies_eighty

#print FrontierFinalEighty.rank_four_upper_eighty_of_intersecting_twenty_seven
#print FrontierFinalEighty.literal_intersecting_twenty_seven_implies_eighty
