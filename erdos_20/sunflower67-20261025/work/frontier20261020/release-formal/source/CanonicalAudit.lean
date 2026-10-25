import CanonicalTwenty
import MeetingDefect
import MinimumTransversals
import TenLinkIntersection
import CompletionCompatibility
import Lean

open Lean Elab Command

private def auditCanonicalRoot (target : Name) : CommandElabM Unit := do
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
  logInfo m!"CANONICAL_AXIOM_AUDIT {receipt.compress}"

syntax (name := canonicalAudit) "#canonical_audit " ident : command
elab_rules : command
  | `(#canonical_audit $target:ident) => auditCanonicalRoot target.getId

#canonical_audit Erdos20DesignNormalForm.ten_isomorphic_canonical
#canonical_audit Erdos20ExtremalTwenty.extremal_twenty_two_disjoint_designs
#canonical_audit FrontierCanonicalTwenty.twenty_two_canonical_designs
#canonical_audit FrontierCanonicalTwenty.high_link_two_canonical_designs
#canonical_audit FrontierMeetingDefect.twice_meeting_add_two_le_degree_sum_add_forty
#canonical_audit FrontierMeetingDefect.twice_card_le_twice_disjoint_add_degree_sum_add_thirty_eight
#canonical_audit FrontierMeetingDefect.sixty_one_degree_sum_sixty_six_has_nine_disjoint
#canonical_audit FrontierMinimumTransversals.two_designs_transversal_six
#canonical_audit FrontierMinimumTransversals.twenty_transversal_six_eq_two_disjoint_members
#canonical_audit FrontierTenLinkIntersection.ten_point_has_block_avoiding_two
#canonical_audit FrontierTenLinkIntersection.ten_point_link_intersecting_subfamily_le_two
#canonical_audit FrontierTenLinkIntersection.two_ten_link_coordinates_card_le_four
#canonical_audit FrontierCompletionCompatibility.intersecting_link_edges_have_shared_block_trace
#canonical_audit FrontierCompletionCompatibility.completion_tail_intersects
#canonical_audit FrontierCompletionCompatibility.split_completions_card_le_four
