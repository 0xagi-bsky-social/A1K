import SunflowerLean.Erdos20DesignNormalForm

namespace Erdos20V12ComponentCertificate
open Erdos20DesignNormalForm

def D : Finset (Finset (Fin 6)) := canonicalTen 0 1 2 3 4 5

def BadExtension (E : Finset (Finset (Fin 6))) : Prop :=
  (∃ R ∈ E, ∃ S ∈ E, R≠S ∧ R ∩ S ∈ D) ∨
  (∃ R ∈ E, ∃ S ∈ E, ∃ T ∈ E,
    R≠S ∧ R≠T ∧ S≠T ∧ R ∩ S=R ∩ T ∧ R ∩ S=S ∩ T)

instance (E : Finset (Finset (Fin 6))) : Decidable (BadExtension E) :=
  inferInstanceAs (Decidable ((∃ R ∈ E, ∃ S ∈ E, R≠S ∧ R ∩ S ∈ D) ∨
    (∃ R ∈ E, ∃ S ∈ E, ∃ T ∈ E,
      R≠S ∧ R≠T ∧ S≠T ∧ R ∩ S=R ∩ T ∧ R ∩ S=S ∩ T)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Every selection of six four-sets on the canonical six-point design has
an explicitly forbidden pair or sunflower triple. This is finite kernel reduction. -/
theorem six_four_sets_bad_extension :
    ∀ E ∈ ((Finset.univ : Finset (Fin 6)).powersetCard 4).powersetCard 6,
      BadExtension E := by
  decide +kernel

end Erdos20V12ComponentCertificate
