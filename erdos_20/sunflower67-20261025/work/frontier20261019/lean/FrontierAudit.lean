import SupportBound
import Support56
import SupportGrid
import PairSix
import SupportFacts
import DegreeEnvelope
import MomentArithmetic
import FourStar
import SupportGrid53
import SupportFinish56
import SupportFinish53
import SupportReduction
import LiteralStatements
import Lean

namespace FrontierAudit
open Lean Elab Command

private def auditRoot (target : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.find? target
    | throwError "FRONTIER_MISSING_ROOT: {target}"
  match info with
  | .thmInfo _ => pure ()
  | _ => throwError "FRONTIER_NOT_THEOREM: {target}"
  unless ← liftTermElabM (Lean.Meta.isProp info.type) do
    throwError "FRONTIER_NOT_PROP: {target}"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms target
  let unexpected := axioms.filter fun name => !allowed.contains name
  unless unexpected.isEmpty do
    throwError "FRONTIER_DISALLOWED: root={target}; unexpected={unexpected.toList}"
  let names := (axioms.map Name.toString).qsort (· < ·)
  let receipt := Json.mkObj [("root",Json.str target.toString), ("axioms",Json.arr (names.map Json.str)), ("status",Json.str "pass")]
  logInfo m!"FRONTIER_AXIOM_AUDIT {receipt.compress}"

syntax (name := frontierAudit) "#frontier_audit " ident : command
elab_rules : command
  | `(#frontier_audit $target:ident) => auditRoot target.getId
end FrontierAudit

#frontier_audit FrontierSupport.weighted_incidence_sum
#frontier_audit FrontierSupport.intersecting_degree_support_inequality
#frontier_audit FrontierSupport.intersecting_twenty_eight_support_le_seventy_two
#frontier_audit FrontierSupport.finite72_obstruction_of_counterexample
#frontier_audit FrontierSupport.intersecting_upper_twenty_seven_iff_no_finite72_obstruction
#frontier_audit FrontierSupport.equal_intersections_iff_no_exact_two
#frontier_audit FrontierSupport56.sum_indicator
#frontier_audit FrontierSupport56.indicator_inter
#frontier_audit FrontierSupport56.double_sum_indicator
#frontier_audit FrontierSupport56.corrected_nonempty
#frontier_audit FrontierSupport56.double_sum_ge_diagonal
#frontier_audit FrontierSupport56.double_sum_corrected_lower
#frontier_audit FrontierSupport56.double_sum_inter_eq
#frontier_audit FrontierSupport56.triple_codegree_le_two
#frontier_audit FrontierSupport56.three_star_sum_bound
#frontier_audit FrontierSupport56.two_star_sum_bound
#frontier_audit FrontierSupport56.three_star_second_moment
#frontier_audit FrontierSupportGrid.grid_bound
#frontier_audit FrontierSupportGrid.natural_grid_bound
#frontier_audit FrontierPairSix.common_point_of_incidence_defect
#frontier_audit FrontierPairSix.thirteen_six_four_common_point
#frontier_audit FrontierPairSix.avoiding_pair_shape
#frontier_audit FrontierPairSix.x_only_card_thirteen
#frontier_audit FrontierPairSix.x_only_point_capacity_four
#frontier_audit FrontierPairSix.pair_avoiding_common_point
#frontier_audit FrontierPairSix.triangle_anchor_multiplicity
#frontier_audit FrontierPairSix.degree_nineteen_pair_six_avoiding_common_point
#frontier_audit FrontierSupportFacts.degree_pos
#frontier_audit FrontierSupportFacts.degree_sum
#frontier_audit FrontierSupportFacts.degree_sum_twenty_eight
#frontier_audit FrontierSupportFacts.pair_bound
#frontier_audit FrontierSupportFacts.triple_bound
#frontier_audit FrontierSupportFacts.two_degree_bound
#frontier_audit FrontierSupportFacts.three_degree_bound
#frontier_audit FrontierSupportFacts.quadratic_sum_eq
#frontier_audit FrontierDegreeEnvelope.exists_top_two
#frontier_audit FrontierDegreeEnvelope.exists_top_three
#frontier_audit FrontierDegreeEnvelope.exists_top_four
#frontier_audit FrontierDegreeEnvelope.degree_envelope
#frontier_audit FrontierDegreeEnvelope.envelope_three
#frontier_audit FrontierDegreeEnvelope.envelope_four
#frontier_audit FrontierDegreeEnvelope.sum_falling_eq_square_sub
#frontier_audit FrontierDegreeEnvelope.support_degree_pos
#frontier_audit FrontierDegreeEnvelope.support_degree_sum
#frontier_audit FrontierMomentArithmetic.falling_factorial_nonneg
#frontier_audit FrontierMomentArithmetic.triple_correction_le_two
#frontier_audit FrontierMomentArithmetic.quadratic_lower_of_sum_bounds
#frontier_audit FrontierMomentArithmetic.three_pair_moment_bound
#frontier_audit FrontierMomentArithmetic.six_pair_moment_bound
#frontier_audit FrontierFourStar.corrected_nonempty
#frontier_audit FrontierFourStar.four_star_second_moment
#frontier_audit FrontierFourStar.four_star_sum_bound
#frontier_audit FrontierFourStar.four_star_twice_sum_bound
#frontier_audit FrontierFourStar.four_degree_sum_le_sixty
#frontier_audit FrontierSupportGrid53.grid_bound
#frontier_audit FrontierSupportGrid53.natural_grid_bound
#frontier_audit FrontierSupportFinish.intersecting_twenty_eight_support_le_fifty_six
#frontier_audit FrontierSupportFinish.intersecting_twenty_eight_support_le_fifty_three
#frontier_audit FrontierSupportReduction.finite56_obstruction_of_counterexample
#frontier_audit FrontierSupportReduction.finite53_obstruction_of_counterexample
#frontier_audit FrontierSupportReduction.intersecting_upper_twenty_seven_iff_no_finite56_obstruction
#frontier_audit FrontierSupportReduction.intersecting_upper_twenty_seven_iff_no_finite53_obstruction
#frontier_audit FrontierLiteralStatements.literal_support56
#frontier_audit FrontierLiteralStatements.literal_support53
#frontier_audit FrontierLiteralStatements.literal_i27_iff_no_fin56
#frontier_audit FrontierLiteralStatements.literal_i27_iff_no_fin53
