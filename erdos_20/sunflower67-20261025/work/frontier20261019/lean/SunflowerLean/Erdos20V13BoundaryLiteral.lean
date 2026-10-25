import SunflowerLean.Erdos20V13Boundary

namespace Erdos20V13BoundaryLiteral
open Erdos20BCWConditional Erdos20DegreeCongruences Erdos20V8Targets
open Erdos20V9Census Erdos20V8Boundary Erdos20V12Profile Erdos20V13Boundary

/-- Entire literal boundary statement: exact rank, all cores (including empty),
three distinct finite-set petals, explicit I27 and actual degree/support counts. -/
theorem conditional_boundary_fully_literal
    (hI : (∀ {β : Type} [DecidableEq β] (G : Finset (Finset β)), (∀ S∈G, S.card=4) → (∀ H : Finset (Finset β), H ⊆ G → ¬ (H.card=3 ∧ ∃ C : Finset β, ∀ S T : Finset β, S∈H → T∈H → S≠T → S∩T=C)) → (∀ S∈G, ∀ T∈G, (S∩T).Nonempty) → G.card≤27))
    {α : Type} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R∈F, R.card=4) (hf : (∀ H : Finset (Finset α), H ⊆ F → ¬ (H.card=3 ∧ ∃ C : Finset α, ∀ S T : Finset α, S∈H → T∈H → S≠T → S∩T=C))) (hc : F.card=81) :
    (F.biUnion id).card=17 ∧ ((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=17))=∅ ∧
    ((((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=18)).card=0 ∧ ((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=19)).card=16 ∧ ((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=20)).card=1) ∨
     (((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=18)).card=1 ∧ ((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=19)).card=14 ∧ ((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=20)).card=2)) ∧
    ((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=20)).card≤2 ∧ (∀ R∈F, (R∩((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=20))).card≤1) := by
  simpa only [support,degreeClass,degree,highPoints,TwoCensusProfiles] using
    Erdos20V12Final.conditional_eighty_one_boundary_rigidity hI F hu hf hc

/-- Entire literal terminal implication. All three mathematical inputs remain
ordinary hypotheses; no certificate for them is supplied by this theorem. -/
theorem unrestricted_eighty_three_inputs_fully_literal
    (hI : (∀ {β : Type} [DecidableEq β] (G : Finset (Finset β)), (∀ S∈G, S.card=4) → (∀ H : Finset (Finset β), H ⊆ G → ¬ (H.card=3 ∧ ∃ C : Finset β, ∀ S T : Finset β, S∈H → T∈H → S≠T → S∩T=C)) → (∀ S∈G, ∀ T∈G, (S∩T).Nonempty) → G.card≤27))
    (hA : ¬ (∃ (α : Type) (_ : DecidableEq α) (F : Finset (Finset α)), (∀ R∈F, R.card=4) ∧ (∀ H : Finset (Finset α), H ⊆ F → ¬ (H.card=3 ∧ ∃ C : Finset α, ∀ S T : Finset α, S∈H → T∈H → S≠T → S∩T=C)) ∧ F.card=81 ∧ (F.biUnion id).card=17 ∧ ((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=17))=∅ ∧ ((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=18)).card=0 ∧ ((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=19)).card=16 ∧ ((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=20)).card=1 ∧ (∀ R∈F, (R∩((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=20))).card≤1)))
    (hB : ¬ (∃ (α : Type) (_ : DecidableEq α) (F : Finset (Finset α)), (∀ R∈F, R.card=4) ∧ (∀ H : Finset (Finset α), H ⊆ F → ¬ (H.card=3 ∧ ∃ C : Finset α, ∀ S T : Finset α, S∈H → T∈H → S≠T → S∩T=C)) ∧ F.card=81 ∧ (F.biUnion id).card=17 ∧ ((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=17))=∅ ∧ ((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=18)).card=1 ∧ ((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=19)).card=14 ∧ ((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=20)).card=2 ∧ (∀ R∈F, (R∩((F.biUnion id).filter (fun x => (F.filter (fun R => x∈R)).card=20))).card≤1))) :
    ∀ {α : Type} [DecidableEq α] (F : Finset (Finset α)),
      (∀ R∈F, R.card=4) → (∀ H : Finset (Finset α), H ⊆ F → ¬ (H.card=3 ∧ ∃ C : Finset α, ∀ S T : Finset α, S∈H → T∈H → S≠T → S∩T=C)) → F.card≤80 := by
  exact unrestricted_eighty_of_three_open_inputs hI hA hB

end Erdos20V13BoundaryLiteral
