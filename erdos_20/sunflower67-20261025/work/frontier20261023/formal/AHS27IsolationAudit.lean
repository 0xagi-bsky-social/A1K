/- Isolation-only audit: excludes the separate AHS sunflower-free construction roots. -/
import AHS27Isolation
import AHS27Construction
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
  logInfo m!"AHS27_AXIOM_AUDIT {receipt.compress}"

syntax (name := ahs27Audit) "#ahs27_audit " ident : command
elab_rules : command
  | `(#ahs27_audit $target:ident) => auditRoot target.getId

#ahs27_audit FrontierAHS27.AHS_card
#ahs27_audit FrontierAHS27.AHS_uniform
#ahs27_audit FrontierAHS27.AHS_intersecting
#ahs27_audit FrontierAHS27.AHS_eq_chooseTwoGroups
#ahs27_audit FrontierAHS27.group_card
#ahs27_audit FrontierAHS27.groups_disjoint
#ahs27_audit FrontierAHS27.groups_cover
#ahs27_audit FrontierAHS27.AHS_support
#ahs27_audit FrontierAHS27.trace_blockers
#ahs27_audit FrontierAHS27.map_trace_subset
#ahs27_audit FrontierAHS27.trace_card_le
#ahs27_audit FrontierAHS27.map_inter_arbitrary
#ahs27_audit FrontierAHS27.extra_trace_not_mem
#ahs27_audit FrontierAHS27.embedded_AHS_extra_disjoint_of_trace_property
#ahs27_audit FrontierAHS27.embedded_AHS_extra_disjoint
#ahs27_audit FrontierAHS27.rank_four_embedded_AHS_extra_disjoint

#print FrontierAHS27.embedded_AHS_extra_disjoint
#print axioms FrontierAHS27.embedded_AHS_extra_disjoint
