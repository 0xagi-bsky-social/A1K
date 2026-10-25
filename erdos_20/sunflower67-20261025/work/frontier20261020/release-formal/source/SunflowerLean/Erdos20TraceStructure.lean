import SunflowerLean.Erdos20SpreadPacking

/-! Maximum-matching trace classes obey cross-intersection constraints.
These elementary exchange lemmas do not assert a new general sunflower bound. -/
namespace Erdos20TraceStructure

/-- A point of a matching member lies in the matching union. -/
theorem mem_matching_union
    {α : Type*} [DecidableEq α] (matching : Finset (Finset α))
    {A : Finset α} {x : α} (hA : A ∈ matching) (hx : x ∈ A) :
    x ∈ matching.biUnion id :=
  Finset.mem_biUnion.mpr ⟨A, hA, hx⟩

/-- A singleton trace on one matching member avoids every other matching member. -/
theorem singleton_trace_disjoint_other
    {α : Type*} [DecidableEq α]
    (matching : Finset (Finset α)) (A S B : Finset α) (x : α)
    (hdis : IsPairwiseDisjoint matching) (hA : A ∈ matching)
    (hxA : x ∈ A) (htrace : S ∩ matching.biUnion id = {x})
    (hB : B ∈ matching) (hBA : B ≠ A) : S ∩ B = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨hzS, hzB⟩ := Finset.mem_inter.mp hz
  have hzx : z = x := by
    have : z ∈ S ∩ matching.biUnion id :=
      Finset.mem_inter.mpr ⟨hzS, mem_matching_union matching hB hzB⟩
    simpa [htrace] using this
  subst z
  have : x ∈ A ∩ B := Finset.mem_inter.mpr ⟨hxA, hzB⟩
  rw [hdis A B hA hB hBA.symm] at this
  exact Finset.notMem_empty x this

private theorem insert_pairwise_disjoint
    {α : Type*} [DecidableEq α]
    (matching : Finset (Finset α)) (S : Finset α)
    (hdis : IsPairwiseDisjoint matching)
    (havoid : ∀ B ∈ matching, S ∩ B = ∅) :
    IsPairwiseDisjoint (insert S matching) := by
  intro A B hA hB hne
  rcases Finset.mem_insert.mp hA with hAS | hAm
  · subst A
    rcases Finset.mem_insert.mp hB with hBS | hBm
    · exact False.elim (hne hBS.symm)
    · exact havoid B hBm
  · rcases Finset.mem_insert.mp hB with hBS | hBm
    · subst B
      rw [Finset.inter_comm]
      exact havoid A hAm
    · exact hdis A B hAm hBm hne

/-- Two singleton trace classes attached to distinct points of the same member of
 a cardinality-maximum matching are cross-intersecting. If they were disjoint,
 replacing that member by the two sets would enlarge the matching. -/
theorem maximum_matching_singleton_traces_intersect
    {α : Type*} [DecidableEq α]
    (family matching : Finset (Finset α)) (A S T : Finset α) (x y : α)
    (hsub : matching ⊆ family) (hdis : IsPairwiseDisjoint matching)
    (hmax : ∀ other : Finset (Finset α), other ⊆ family → IsPairwiseDisjoint other →
      other.card ≤ matching.card)
    (hA : A ∈ matching) (hxA : x ∈ A) (hyA : y ∈ A) (hxy : x ≠ y)
    (hS : S ∈ family) (hT : T ∈ family)
    (htraceS : S ∩ matching.biUnion id = {x})
    (htraceT : T ∩ matching.biUnion id = {y}) :
    (S ∩ T).Nonempty := by
  classical
  have hxS : x ∈ S := by
    have : x ∈ S ∩ matching.biUnion id := by rw [htraceS]; simp
    exact (Finset.mem_inter.mp this).1
  have hyT : y ∈ T := by
    have : y ∈ T ∩ matching.biUnion id := by rw [htraceT]; simp
    exact (Finset.mem_inter.mp this).1
  have hSneT : S ≠ T := by
    intro hST
    have : x = y := by
      have : x ∈ T ∩ matching.biUnion id := by
        rw [← hST, htraceS]
        simp
      simpa [htraceT] using this
    exact hxy this
  have hSavoid : ∀ B ∈ matching.erase A, S ∩ B = ∅ := by
    intro B hB
    obtain ⟨hBA, hBm⟩ := Finset.mem_erase.mp hB
    exact singleton_trace_disjoint_other matching A S B x hdis hA hxA htraceS hBm hBA
  have hTavoid : ∀ B ∈ matching.erase A, T ∩ B = ∅ := by
    intro B hB
    obtain ⟨hBA, hBm⟩ := Finset.mem_erase.mp hB
    exact singleton_trace_disjoint_other matching A T B y hdis hA hyA htraceT hBm hBA
  have hSnot : S ∉ matching.erase A := by
    intro hSm
    have : x ∈ S ∩ S := Finset.mem_inter.mpr ⟨hxS, hxS⟩
    rw [hSavoid S hSm] at this
    exact Finset.notMem_empty x this
  have hTnot : T ∉ matching.erase A := by
    intro hTm
    have : y ∈ T ∩ T := Finset.mem_inter.mpr ⟨hyT, hyT⟩
    rw [hTavoid T hTm] at this
    exact Finset.notMem_empty y this
  by_contra hnot
  have hSTempty : S ∩ T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
  have herased : IsPairwiseDisjoint (matching.erase A) := by
    intro B C hB hC hne
    exact hdis B C (Finset.mem_of_mem_erase hB) (Finset.mem_of_mem_erase hC) hne
  have hnewdis : IsPairwiseDisjoint (insert S (insert T (matching.erase A))) := by
    apply insert_pairwise_disjoint
    · exact insert_pairwise_disjoint (matching.erase A) T herased hTavoid
    · intro B hB
      rcases Finset.mem_insert.mp hB with rfl | hB
      · exact hSTempty
      · exact hSavoid B hB
  have hnewsub : insert S (insert T (matching.erase A)) ⊆ family := by
    intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact hS
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact hT
    exact hsub (Finset.mem_of_mem_erase hB)
  have hbound := hmax _ hnewsub hnewdis
  have hSnotinsert : S ∉ insert T (matching.erase A) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hSneT, hSnot⟩
  rw [Finset.card_insert_of_notMem hSnotinsert,
    Finset.card_insert_of_notMem hTnot, Finset.card_erase_of_mem hA] at hbound
  have hMpos : 0 < matching.card := Finset.card_pos.mpr ⟨A, hA⟩
  omega

/-- The forced intersection lies outside the matching union, hence in the two
residual sets obtained by deleting their singleton traces. -/
theorem maximum_matching_singleton_residuals_intersect
    {α : Type*} [DecidableEq α]
    (family matching : Finset (Finset α)) (A S T : Finset α) (x y : α)
    (hsub : matching ⊆ family) (hdis : IsPairwiseDisjoint matching)
    (hmax : ∀ other : Finset (Finset α), other ⊆ family → IsPairwiseDisjoint other →
      other.card ≤ matching.card)
    (hA : A ∈ matching) (hxA : x ∈ A) (hyA : y ∈ A) (hxy : x ≠ y)
    (hS : S ∈ family) (hT : T ∈ family)
    (htraceS : S ∩ matching.biUnion id = {x})
    (htraceT : T ∩ matching.biUnion id = {y}) :
    ((S \ {x}) ∩ (T \ {y})).Nonempty := by
  obtain ⟨z, hz⟩ := maximum_matching_singleton_traces_intersect
    family matching A S T x y hsub hdis hmax hA hxA hyA hxy hS hT htraceS htraceT
  obtain ⟨hzS, hzT⟩ := Finset.mem_inter.mp hz
  have hzout : z ∉ matching.biUnion id := by
    intro hzU
    have hzx : z = x := by
      have := Finset.mem_inter.mpr ⟨hzS, hzU⟩
      simpa [htraceS] using this
    have hzy : z = y := by
      have := Finset.mem_inter.mpr ⟨hzT, hzU⟩
      simpa [htraceT] using this
    exact hxy (hzx.symm.trans hzy)
  refine ⟨z, Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hzS, ?_⟩,
    Finset.mem_sdiff.mpr ⟨hzT, ?_⟩⟩⟩
  · intro hz
    have hzx : z = x := Finset.mem_singleton.mp hz
    exact hzout (hzx ▸ mem_matching_union matching hA hxA)
  · intro hz
    have hzy : z = y := Finset.mem_singleton.mp hz
    exact hzout (hzy ▸ mem_matching_union matching hA hyA)

/-- A three-edge family showing that inclusion-maximal is too weak. -/
def maximalBoundaryFamily : Finset (Finset (Fin 4)) :=
  {{0, 1}, {0, 2}, {1, 3}}

/-- The central edge alone is inclusion-maximal, but not maximum. -/
def maximalBoundaryMatching : Finset (Finset (Fin 4)) := {{0, 1}}

/-- A checked boundary witness: an inclusion-maximal matching admits two disjoint
singleton-trace residuals, and a strictly larger matching exists. -/
theorem inclusion_maximal_does_not_force_residual_intersection :
    maximalBoundaryMatching ⊆ maximalBoundaryFamily ∧
    IsPairwiseDisjoint maximalBoundaryMatching ∧
    (∀ other : Finset (Finset (Fin 4)),
      maximalBoundaryMatching ⊆ other → other ⊆ maximalBoundaryFamily →
      IsPairwiseDisjoint other → other = maximalBoundaryMatching) ∧
    ({0, 2} : Finset (Fin 4)) ∩ maximalBoundaryMatching.biUnion id = {0} ∧
    ({1, 3} : Finset (Fin 4)) ∩ maximalBoundaryMatching.biUnion id = {1} ∧
    ¬((({0, 2} : Finset (Fin 4)) \ {0}) ∩ ({1, 3} \ {1})).Nonempty ∧
    ∃ other : Finset (Finset (Fin 4)), other ⊆ maximalBoundaryFamily ∧
      IsPairwiseDisjoint other ∧ maximalBoundaryMatching.card < other.card := by
  refine ⟨by decide, by unfold IsPairwiseDisjoint; decide, ?_, by decide, by decide, by decide, ?_⟩
  · intro other hsub hfamily hdis
    apply Finset.Subset.antisymm ?_ hsub
    intro S hS
    have hcases : S = {0, 1} ∨ S = {0, 2} ∨ S = {1, 3} := by
      simpa [maximalBoundaryFamily] using hfamily hS
    have hbase : ({0, 1} : Finset (Fin 4)) ∈ other := hsub (by decide)
    rcases hcases with rfl | rfl | rfl
    · decide
    · have hbad := hdis {0, 2} {0, 1} hS hbase (by decide)
      have hfalse : ({0, 2} : Finset (Fin 4)) ∩ {0, 1} ≠ ∅ := by decide
      exact False.elim (hfalse hbad)
    · have hbad := hdis {1, 3} {0, 1} hS hbase (by decide)
      have hfalse : ({1, 3} : Finset (Fin 4)) ∩ {0, 1} ≠ ∅ := by decide
      exact False.elim (hfalse hbad)
  · exact ⟨{{0, 2}, {1, 3}}, by decide, by unfold IsPairwiseDisjoint; decide, by decide⟩

#print axioms inclusion_maximal_does_not_force_residual_intersection
#print axioms maximum_matching_singleton_traces_intersect
#print axioms maximum_matching_singleton_residuals_intersect
end Erdos20TraceStructure
