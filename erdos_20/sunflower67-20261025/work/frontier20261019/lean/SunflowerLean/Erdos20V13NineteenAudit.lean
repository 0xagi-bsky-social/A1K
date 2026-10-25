import SunflowerLean.Erdos20V13Nineteen
import SunflowerLean.Erdos20V13Intersecting
import SunflowerLean.Erdos20V13Endpoint
import Lean

namespace Erdos20V13NineteenAudit
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

syntax (name := v13NineteenAudit) "#v13_nineteen_audit " ident : command
elab_rules : command
  | `(#v13_nineteen_audit $target:ident) => auditRoot target.getId
end Erdos20V13NineteenAudit



#v13_nineteen_audit Erdos20V13Nineteen.nineteen_max_degree_five_transversal_ge_six
#v13_nineteen_audit Erdos20V13Nineteen.nineteen_transversal_five_has_degree_six
#v13_nineteen_audit Erdos20V13Nineteen.max_degree_iff_on_support
#v13_nineteen_audit Erdos20V13Nineteen.nineteen_max_degree_five_exists_transversal_six
#v13_nineteen_audit Erdos20V13Nineteen.nineteen_max_degree_five_transversal_exact_six
#v13_nineteen_audit Erdos20V13Intersecting.star_union_card_add_pair_codegree
#v13_nineteen_audit Erdos20V13Intersecting.degree_nineteen_pair_six_partner_bounds
#v13_nineteen_audit Erdos20V13Intersecting.intersecting_twenty_eight_degree_nineteen_partner_bounds
#v13_nineteen_audit Erdos20V13Intersecting.upperStar_eq_image_restore_core
#v13_nineteen_audit Erdos20V13Intersecting.pair_codegree_six_exact_two_triangles
#v13_nineteen_audit Erdos20V13Endpoint.liftTriple_injective
#v13_nineteen_audit Erdos20V13Endpoint.family_card
#v13_nineteen_audit Erdos20V13Endpoint.family_uniform
#v13_nineteen_audit Erdos20V13Endpoint.family_intersecting
#v13_nineteen_audit Erdos20V13Endpoint.family_sunflower_free
#v13_nineteen_audit Erdos20V13Endpoint.center_degree_nineteen
#v13_nineteen_audit Erdos20V13Endpoint.center_pair_degree_le_five
#v13_nineteen_audit Erdos20V13Endpoint.nineteen_member_endpoint_counterexample
#v13_nineteen_audit Erdos20BCWConditional.core_union_injOn_residualLink
