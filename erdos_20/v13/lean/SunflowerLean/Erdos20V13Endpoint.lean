import SunflowerLean.Erdos20Substitution
import SunflowerLean.Erdos20DegreeCongruences

namespace Erdos20V13Endpoint
open Erdos20TripleWitness Erdos20BCWConditional Erdos20DegreeCongruences

/-- Delete the first block of the inherited twenty-triple witness. -/
def nineteenTriples : Finset (Finset (Fin 12)) := twentyTriples.erase {0,1,2}

/-- Adjoin a fresh common center, represented by none. -/
def liftTriple (S : Finset (Fin 12)) : Finset (Option (Fin 12)) :=
  insert none (S.image some)

def family : Finset (Finset (Option (Fin 12))) := nineteenTriples.image liftTriple

theorem liftTriple_injective : Function.Injective liftTriple := by
  intro S T he
  apply Finset.ext
  intro x
  have hh := congrArg (fun R : Finset (Option (Fin 12)) => some x ∈ R) he
  simpa [liftTriple] using Iff.of_eq hh

theorem family_card : family.card=19 := by
  rw [family,Finset.card_image_of_injective _ liftTriple_injective]
  decide

theorem family_uniform : ∀ S ∈ family, S.card=4 := by
  intro S hS
  obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
  have hu := twentyTriples_uniform T ((Finset.mem_erase.mp hT).2)
  simp [liftTriple,Finset.card_image_of_injective T (Option.some_injective (Fin 12)),hu]

theorem family_intersecting : ∀ S ∈ family, ∀ T ∈ family, (S ∩ T).Nonempty := by
  intro S hS T hT
  obtain ⟨A,_,rfl⟩ := Finset.mem_image.mp hS
  obtain ⟨B,_,rfl⟩ := Finset.mem_image.mp hT
  exact ⟨none,by simp [liftTriple]⟩

theorem family_sunflower_free : IsSunflowerFree family 3 := by
  apply sunflowerFree_of_no_triple
  intro S hS T hT U hU hST hSU hTU hh
  obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hS
  obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hT
  obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hU
  have h1 : A ∩ B = A ∩ C := by
    apply Finset.ext
    intro x
    have he := congrArg (fun R : Finset (Option (Fin 12)) => some x ∈ R) hh.1
    simpa [liftTriple] using Iff.of_eq he
  have h2 : A ∩ B = B ∩ C := by
    apply Finset.ext
    intro x
    have he := congrArg (fun R : Finset (Option (Fin 12)) => some x ∈ R) hh.2
    simpa [liftTriple] using Iff.of_eq he
  have he := Erdos20Substitution.three_rigidity twentyTriples 3 twentyTriples_uniform
    twentyTriples_sunflower_free (Finset.mem_erase.mp hA).2
    (Finset.mem_erase.mp hB).2 (Finset.mem_erase.mp hC).2 h1 h2
  exact hST (congrArg liftTriple he.1)

theorem center_degree_nineteen : degree family none=19 := by
  have he : family.filter (fun S => none ∈ S)=family := by
    apply Finset.filter_eq_self.mpr
    intro S hS
    obtain ⟨T,_,rfl⟩ := Finset.mem_image.mp hS
    simp [liftTriple]
  change (family.filter (fun S => none ∈ S)).card=19
  rw [he,family_card]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The concrete center pairs all have codegree at most five. Ordinary decide
is reduced by Lean's kernel; no native_decide or external solver is used. -/
theorem center_pair_degree_le_five :
    ∀ y : Option (Fin 12), none ≠ y → (upperStar family {none,y}).card≤5 := by
  decide

/-- A concrete 19-member counterexample to lowering the 20-member hypothesis
in the inherited degree-nineteen/codegree-six corollary. -/
theorem nineteen_member_endpoint_counterexample :
    family.card=19 ∧ (∀ S ∈ family, S.card=4) ∧ IsSunflowerFree family 3 ∧
    (∀ S ∈ family, ∀ T ∈ family, (S ∩ T).Nonempty) ∧
    degree family none=19 ∧
    ¬ ∃ y : Option (Fin 12), none ≠ y ∧ (upperStar family {none,y}).card=6 := by
  refine ⟨family_card,family_uniform,family_sunflower_free,family_intersecting,
    center_degree_nineteen,?_⟩
  rintro ⟨y,hne,hc⟩
  have h := center_pair_degree_le_five y hne
  omega

end Erdos20V13Endpoint

#print axioms Erdos20V13Endpoint.liftTriple_injective
#print axioms Erdos20V13Endpoint.family_card
#print axioms Erdos20V13Endpoint.family_uniform
#print axioms Erdos20V13Endpoint.family_intersecting
#print axioms Erdos20V13Endpoint.family_sunflower_free
#print axioms Erdos20V13Endpoint.center_degree_nineteen
#print axioms Erdos20V13Endpoint.center_pair_degree_le_five
#print axioms Erdos20V13Endpoint.nineteen_member_endpoint_counterexample
