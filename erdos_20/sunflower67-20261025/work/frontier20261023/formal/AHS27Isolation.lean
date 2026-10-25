import AHS27Transport
import AHS27Trace

namespace FrontierAHS27
open Erdos20FiniteReduction
universe u

/-- A fully proved isolation theorem on arbitrary ground types. -/
theorem embedded_AHS_extra_disjoint
    {α : Type u} [DecidableEq α]
    (e : Fin 9 ↪ α) (F : Finset (Finset α))
    (hfree : IsSunflowerFree F 3) (hcontain : mapFamily e AHS ⊆ F)
    (C : Finset α) (hC : C ∈ F) (hcard : C.card ≤ 4)
    (hout : C ∉ mapFamily e AHS) : Disjoint C (blockSupport e) :=
  embedded_AHS_extra_disjoint_of_trace_property trace_blockers e F hfree hcontain C hC hcard hout

/-- Rank-four specialization in the project's usual sunflower-free vocabulary. -/
theorem rank_four_embedded_AHS_extra_disjoint
    {α : Type u} [DecidableEq α]
    (e : Fin 9 ↪ α) (F : Finset (Finset α))
    (hu : ∀ C ∈ F, C.card = 4) (hfree : IsSunflowerFree F 3)
    (hcontain : mapFamily e AHS ⊆ F) :
    ∀ C ∈ F \ mapFamily e AHS, Disjoint C (blockSupport e) := by
  intro C hC
  obtain ⟨hCF, hout⟩ := Finset.mem_sdiff.mp hC
  exact embedded_AHS_extra_disjoint e F hfree hcontain C hCF
    (by rw [hu C hCF]) hout

end FrontierAHS27
