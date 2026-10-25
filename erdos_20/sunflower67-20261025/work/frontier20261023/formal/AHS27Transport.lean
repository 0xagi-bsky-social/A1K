import AHS27Data

namespace FrontierAHS27

open Erdos20FiniteReduction

universe u

/-- The finite nine-point support of an embedded configuration. -/
def blockSupport {α : Type u} (e : Fin 9 ↪ α) : Finset α := Finset.univ.map e

/-- Restrict an arbitrary set to the embedded nine-point support and pull it back. -/
def trace {α : Type u} [DecidableEq α] (e : Fin 9 ↪ α) (C : Finset α) :
    Finset (Fin 9) := Finset.univ.filter (fun i => e i ∈ C)

@[simp] theorem mem_trace {α : Type u} [DecidableEq α]
    (e : Fin 9 ↪ α) (C : Finset α) (i : Fin 9) :
    i ∈ trace e C ↔ e i ∈ C := by simp [trace]

theorem map_trace_subset {α : Type u} [DecidableEq α]
    (e : Fin 9 ↪ α) (C : Finset α) : (trace e C).map e ⊆ C := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
  exact (mem_trace e C i).mp hi

theorem trace_card_le {α : Type u} [DecidableEq α]
    (e : Fin 9 ↪ α) (C : Finset α) : (trace e C).card ≤ C.card := by
  simpa using Finset.card_le_card (map_trace_subset e C)

/-- Intersections of an embedded block with an arbitrary member depend exactly
on its trace, even if that member has points outside the nine-point support. -/
theorem map_inter_arbitrary {α : Type u} [DecidableEq α]
    (e : Fin 9 ↪ α) (A : Finset (Fin 9)) (C : Finset α) :
    A.map e ∩ C = (A ∩ trace e C).map e := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxA, hxC⟩ := Finset.mem_inter.mp hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hxA
    exact Finset.mem_map.mpr ⟨i, Finset.mem_inter.mpr
      ⟨hi, (mem_trace e C i).mpr hxC⟩, rfl⟩
  · intro hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨hiA, hiT⟩ := Finset.mem_inter.mp hi
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_map.mpr ⟨i, hiA, rfl⟩, (mem_trace e C i).mp hiT⟩

/-- A rank-at-most-four extra member cannot have a trace that is already a block. -/
theorem extra_trace_not_mem {α : Type u} [DecidableEq α]
    (e : Fin 9 ↪ α) (C : Finset α) (hcard : C.card ≤ 4)
    (hout : C ∉ mapFamily e AHS) : trace e C ∉ AHS := by
  intro hT
  have hTc := AHS_uniform _ hT
  have heq : (trace e C).map e = C := Finset.eq_of_subset_of_card_le
    (map_trace_subset e C) (by simpa [hTc] using hcard)
  apply hout
  rw [← heq]
  exact Finset.mem_map.mpr ⟨trace e C, hT, rfl⟩

/-- Full arbitrary-type isolation theorem. A family may have unbounded ambient
support; only the tested extra member has rank at most four. -/
theorem embedded_AHS_extra_disjoint_of_trace_property
    (hblock : ∀ T : Finset (Fin 9), T.Nonempty → T.card ≤ 4 → T ∉ AHS →
      ∃ A ∈ AHS, ∃ B ∈ AHS, A ≠ B ∧
        A ∩ B = A ∩ T ∧ A ∩ B = B ∩ T)
    {α : Type u} [DecidableEq α]
    (e : Fin 9 ↪ α) (F : Finset (Finset α))
    (hfree : IsSunflowerFree F 3) (hcontain : mapFamily e AHS ⊆ F)
    (C : Finset α) (hC : C ∈ F) (hcard : C.card ≤ 4)
    (hout : C ∉ mapFamily e AHS) : Disjoint C (blockSupport e) := by
  rw [Finset.disjoint_left]
  intro x hxC hxS
  obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hxS
  have hnonempty : (trace e C).Nonempty :=
    ⟨i, (mem_trace e C i).mpr (by simpa [hi] using hxC)⟩
  obtain ⟨A, hA, B, hB, hAB, hAT, hBT⟩ :=
    hblock (trace e C) hnonempty
      ((trace_card_le e C).trans hcard) (extra_trace_not_mem e C hcard hout)
  have hAmem : A.map e ∈ mapFamily e AHS := Finset.mem_map.mpr ⟨A, hA, rfl⟩
  have hBmem : B.map e ∈ mapFamily e AHS := Finset.mem_map.mpr ⟨B, hB, rfl⟩
  have hAB' : A.map e ≠ B.map e := fun heq => hAB (Finset.map_injective e heq)
  have hAC : A.map e ≠ C := fun heq => hout (heq ▸ hAmem)
  have hBC : B.map e ≠ C := fun heq => hout (heq ▸ hBmem)
  have hsun : IsSunflower {A.map e, B.map e, C} 3 := by
    apply Erdos20RankThree.sunflower_three_of_intersections
      (A.map e) (B.map e) C ((A ∩ B).map e) hAB' hAC hBC
    · exact (Finset.map_inter A B).symm
    · rw [map_inter_arbitrary, ← hAT]
    · rw [map_inter_arbitrary, ← hBT]
  apply hfree {A.map e, B.map e, C} _ hsun
  intro D hD
  simp only [Finset.mem_insert, Finset.mem_singleton] at hD
  rcases hD with rfl | rfl | rfl
  · exact hcontain hAmem
  · exact hcontain hBmem
  · exact hC


end FrontierAHS27
