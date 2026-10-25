import SunflowerLean.Erdos20V11EdgeThirdSupport
import SunflowerLean.Erdos20V11EdgeTrace

namespace Erdos20V11EdgeThird
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20V8Boundary Erdos20DegreeCongruences Erdos20V9HighGraph
open Erdos20V10HighTriangle Erdos20V11HighSupport

/-- The actual link of a third high point avoids the five low residual points
of a high edge. The zero-or-two trace restriction is discharged, not assumed. -/
theorem high_edge_third_high_support_disjoint {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) (y : α) (hy : y ∈ highNeighbors F x)
    (z : α) (hz : z ∈ highPoints F) (hxz : x ≠ z) (hyz : y ≠ z) :
    Disjoint (support (residualLink F {z})) (edgeSupport F x y) :=
  third_high_support_disjoint_of_edge_trace F hu hf x hx y hy
    (Erdos20V11EdgeTrace.high_edge_member_trace_zero_or_two F hu hf x hx y hy) z hz hxz hyz

/-- A high edge together with any third high point forces at least twenty
supported points. This unconditional structural obstruction has no intersecting
upper-bound or cardinality81 premise. -/
theorem high_edge_third_high_support_ge_twenty {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) (y : α) (hy : y ∈ highNeighbors F x)
    (z : α) (hz : z ∈ highPoints F) (hxz : x ≠ z) (hyz : y ≠ z) :
    20 ≤ (support F).card :=
  twenty_le_support_of_edge_trace_and_third_high F hu hf x hx y hy
    (Erdos20V11EdgeTrace.high_edge_member_trace_zero_or_two F hu hf x hx y hy) z hz hxz hyz

end Erdos20V11EdgeThird
