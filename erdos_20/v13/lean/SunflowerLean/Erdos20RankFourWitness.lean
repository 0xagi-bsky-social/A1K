import SunflowerLean.Erdos20IteratedLower
import SunflowerLean.Erdos20CrossBounds

/-! Classical rank-four witnesses, obtained structurally from triangle substitution. -/
namespace Erdos20RankFourWitness
open Erdos20CrossBounds Erdos20Substitution Erdos20IteratedLower Erdos20LocalStructure

theorem triangle_intersecting_witness : IntersectingFreeWitness 2 3 := by
  obtain ⟨hu,hf,hi,hc⟩ := cross_intersecting_joint_bound_sharp
  exact ⟨Fin 6, inferInstance, jointSharpTriangle, hu, hf, by omega, hi⟩

/-- The outer and inner triangle have three choices each, giving3*3² members. -/
theorem twenty_seven_intersecting_witness : IntersectingFreeWitness 4 27 := by
  simpa using intersecting_witness_substitution triangle_intersecting_witness
    triangle_intersecting_witness

theorem fifty_four_witness : UniformFreeWitness.{0} 3 4 54 := by
  simpa using double_intersecting_witness twenty_seven_intersecting_witness

/-- Exact products interpolate known lower witnesses at every rank4a+3b. -/
theorem mixed_rank_witness (a b : ℕ) :
    UniformFreeWitness.{0} 3 (4 * a + 3 * b) (54 ^ a * 20 ^ b) := by
  exact tensor_witness (tensor_power_witness (by decide) fifty_four_witness a)
    (tensor_power_witness (by decide)
      ⟨Fin 12, inferInstance, Erdos20TripleWitness.twentyTriples,
        Erdos20TripleWitness.twentyTriples_uniform,
        Erdos20TripleWitness.twentyTriples_sunflower_free,
        Erdos20TripleWitness.twentyTriples_card⟩ b)

end Erdos20RankFourWitness
