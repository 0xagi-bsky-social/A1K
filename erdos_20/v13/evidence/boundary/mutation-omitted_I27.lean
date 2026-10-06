import SunflowerLean.Erdos20V13Boundary

namespace Erdos20V13BoundaryLiteral
open Erdos20BCWConditional Erdos20DegreeCongruences Erdos20V8Targets
open Erdos20V9Census Erdos20V8Boundary Erdos20V12Profile Erdos20V13Boundary

/-- Entire literal boundary statement: exact rank, all cores (including empty),
three distinct finite-set petals, explicit I27 and actual degree/support counts. -/
theorem conditional_boundary_fully_literal
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R∈F, R.card=4) (hf : (∀ H : Finset (Finset α), H ⊆ F → ¬ (H.card=3 ∧ ∃ C : Finset α, ∀ S T : Finset α, S∈H → T∈H → S≠T → S∩T=C))) (hc : F.card=81) :
    (F.biUnion id).card=17 ∧ ((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=17))=∅ ∧
    ((((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=18)).card=0 ∧ ((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=19)).card=16 ∧ ((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=20)).card=1) ∨
     (((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=18)).card=1 ∧ ((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=19)).card=14 ∧ ((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=20)).card=2)) ∧
    ((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=20)).card≤2 ∧ (∀ R∈F, (R∩((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=20))).card≤1) := by
  simpa only [support,degreeClass,degree,highPoints,TwoCensusProfiles] using
    Erdos20V12Final.conditional_eighty_one_boundary_rigidity (by assumption) F hu hf hc


end Erdos20V13BoundaryLiteral
