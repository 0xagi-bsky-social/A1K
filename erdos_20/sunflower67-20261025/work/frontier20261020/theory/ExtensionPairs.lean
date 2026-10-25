import SunflowerLean.Erdos20DesignNormalForm

namespace FrontierExtensionPairs
open Erdos20DesignNormalForm

def canonicalDesign : Finset (Finset (Fin 6)) := canonicalTen 0 1 2 3 4 5

def extensionPair (P : Finset (Fin 6)) : Finset (Fin 6) :=
  Finset.univ.filter (fun q => q ∉ P ∧ insert q P ∈ canonicalDesign)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
/-- Every pair has exactly two distinct extensions in the fixed design.
The finite computation is reduced in Lean's kernel. -/
theorem extension_pair_card_two :
    ∀ P : Finset (Fin 6), P.card = 2 → (extensionPair P).card = 2 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
/-- The two extensions identify the original pair uniquely. This checks all
pairs of subsets, retaining the literal cardinality premises. -/
theorem extension_pair_injective :
    ∀ P Q : Finset (Fin 6), P.card = 2 → Q.card = 2 →
      extensionPair P = extensionPair Q → P = Q := by
  decide

end FrontierExtensionPairs

#print axioms FrontierExtensionPairs.extension_pair_card_two
#print axioms FrontierExtensionPairs.extension_pair_injective
