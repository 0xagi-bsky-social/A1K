import AHS27Data
namespace FrontierAHS27
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
theorem AHS_no_sunflower_triple :
    ∀ S ∈ AHS, ∀ T ∈ AHS, ∀ U ∈ AHS,
      S ≠ T → S ≠ U → T ≠ U →
      ¬ (S ∩ T = S ∩ U ∧ S ∩ T = T ∩ U) := by decide +kernel

theorem AHS_sunflowerFree : IsSunflowerFree AHS 3 :=
  Erdos20TripleWitness.sunflowerFree_of_no_triple AHS AHS_no_sunflower_triple


end FrontierAHS27
