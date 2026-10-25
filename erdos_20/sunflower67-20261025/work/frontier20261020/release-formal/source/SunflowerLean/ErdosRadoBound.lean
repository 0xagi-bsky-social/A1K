import SunflowerLean.Basic

/-!
# The classical Erdős--Rado factorial bound

This file constructs a greedy pairwise-disjoint subfamily whose union hits the
original family, bounds the resulting transversal by `r * (k - 1)`, and closes
the classical factorial induction.
-/

namespace Erdos20Classical

/-- Every finite family of nonempty finite sets has a pairwise-disjoint
subfamily whose union meets every member of the original family. -/
theorem exists_pairwiseDisjoint_hitting_subfamily
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α))
    (hnonempty : ∀ S ∈ family, S.Nonempty) :
    ∃ matching : Finset (Finset α),
      matching ⊆ family ∧
      IsPairwiseDisjoint matching ∧
      ∀ S ∈ family, (S ∩ matching.biUnion id).Nonempty := by
  classical
  revert hnonempty
  induction family using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨∅, ?_, ?_, ?_⟩
      · simp
      · simp [IsPairwiseDisjoint]
      · simp
  | @insert A family hA ih =>
      intro hnonempty
      have hfamily_nonempty : ∀ S ∈ family, S.Nonempty := by
        intro S hS
        exact hnonempty S (Finset.mem_insert_of_mem hS)
      rcases ih hfamily_nonempty with
        ⟨matching, hmatching_sub, hmatching_disjoint, hmatching_hits⟩
      by_cases hA_hits : (A ∩ matching.biUnion id).Nonempty
      · refine ⟨matching, ?_, hmatching_disjoint, ?_⟩
        · exact Finset.Subset.trans hmatching_sub (Finset.subset_insert A family)
        · intro S hS
          rcases Finset.mem_insert.mp hS with hSA | hSfamily
          · simpa [hSA] using hA_hits
          · exact hmatching_hits S hSfamily
      · have hA_nonempty : A.Nonempty :=
          hnonempty A (Finset.mem_insert_self A family)
        have hA_disjoint : ∀ T ∈ matching, A ∩ T = ∅ := by
          intro T hT
          apply Finset.not_nonempty_iff_eq_empty.mp
          intro hAT
          apply hA_hits
          rcases hAT with ⟨x, hxAT⟩
          have hxAT' := Finset.mem_inter.mp hxAT
          exact ⟨x, Finset.mem_inter.mpr
            ⟨hxAT'.1, Finset.mem_biUnion.mpr ⟨T, hT, hxAT'.2⟩⟩⟩
        refine ⟨insert A matching, ?_, ?_, ?_⟩
        · intro S hS
          rcases Finset.mem_insert.mp hS with hSA | hSmatching
          · simpa [hSA]
          · exact Finset.mem_insert_of_mem (hmatching_sub hSmatching)
        · intro S T hS hT hne
          rcases Finset.mem_insert.mp hS with hSA | hSmatching
          · subst S
            rcases Finset.mem_insert.mp hT with hTA | hTmatching
            · subst T
              exact (hne rfl).elim
            · exact hA_disjoint T hTmatching
          · rcases Finset.mem_insert.mp hT with hTA | hTmatching
            · subst T
              simpa [Finset.inter_comm] using hA_disjoint S hSmatching
            · exact hmatching_disjoint S T hSmatching hTmatching hne
        · intro S hS
          rcases Finset.mem_insert.mp hS with hSA | hSfamily
          · subst S
            rcases hA_nonempty with ⟨x, hxA⟩
            exact ⟨x, Finset.mem_inter.mpr ⟨hxA,
              Finset.mem_biUnion.mpr
                ⟨A, Finset.mem_insert_self A matching, hxA⟩⟩⟩
          · rcases hmatching_hits S hSfamily with ⟨x, hx⟩
            have hx' := Finset.mem_inter.mp hx
            rcases Finset.mem_biUnion.mp hx'.2 with ⟨T, hT, hxT⟩
            exact ⟨x, Finset.mem_inter.mpr ⟨hx'.1,
              Finset.mem_biUnion.mpr
                ⟨T, Finset.mem_insert_of_mem hT, hxT⟩⟩⟩

/-- A pairwise-disjoint subfamily of a `k`-sunflower-free family has fewer
than `k` members. -/
theorem pairwiseDisjoint_card_lt_forbidden
    {α : Type*} [DecidableEq α]
    (family matching : Finset (Finset α)) (k : ℕ)
    (hmatching_sub : matching ⊆ family)
    (hmatching_disjoint : IsPairwiseDisjoint matching)
    (hfree : IsSunflowerFree family k) :
    matching.card < k := by
  by_contra hnot
  have hk : k ≤ matching.card := Nat.le_of_not_gt hnot
  obtain ⟨subfamily, hsubfamily, hsubfamily_card⟩ :=
    Finset.exists_subset_card_eq hk
  apply hfree subfamily
    (Finset.Subset.trans hsubfamily hmatching_sub)
  exact disjoint_is_sunflower subfamily k hsubfamily_card
    (fun S T hS hT hne =>
      hmatching_disjoint S T (hsubfamily hS) (hsubfamily hT) hne)

/-- The bounded-transversal step used by the classical Erdős--Rado
factorial induction: a positive `r`-uniform `k`-sunflower-free family has a
hitting set of cardinality at most `r * (k - 1)`. -/
theorem exists_bounded_hitting_set
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r k : ℕ)
    (hr : 1 ≤ r)
    (huniform : ∀ S ∈ family, S.card = r)
    (hfree : IsSunflowerFree family k) :
    ∃ hitting : Finset α,
      hitting.card ≤ r * (k - 1) ∧
      ∀ S ∈ family, ∃ x ∈ hitting, x ∈ S := by
  have hnonempty : ∀ S ∈ family, S.Nonempty := by
    intro S hS
    apply Finset.card_pos.mp
    rw [huniform S hS]
    exact hr
  rcases exists_pairwiseDisjoint_hitting_subfamily family hnonempty with
    ⟨matching, hmatching_sub, hmatching_disjoint, hmatching_hits⟩
  have hmatching_card : matching.card ≤ k - 1 := by
    have hlt := pairwiseDisjoint_card_lt_forbidden family matching k
      hmatching_sub hmatching_disjoint hfree
    omega
  refine ⟨matching.biUnion id, ?_, ?_⟩
  · calc
      (matching.biUnion id).card ≤
          ∑ S ∈ matching, S.card := Finset.card_biUnion_le
      _ = ∑ _S ∈ matching, r := by
          apply Finset.sum_congr rfl
          intro S hS
          exact huniform S (hmatching_sub hS)
      _ = r * matching.card := by simp [Nat.mul_comm]
      _ ≤ r * (k - 1) := Nat.mul_le_mul_left r hmatching_card
  · intro S hS
    rcases hmatching_hits S hS with ⟨x, hx⟩
    have hx' := Finset.mem_inter.mp hx
    exact ⟨x, hx'.2, hx'.1⟩

/-- The classical Erdős--Rado factorial upper bound, stated directly for a
finite uniform sunflower-free family. -/
theorem erdos_rado_factorial_bound
    {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (r k : ℕ)
    (huniform : ∀ S ∈ family, S.card = r)
    (hfree : IsSunflowerFree family k) :
    family.card ≤ (k - 1) ^ r * r.factorial := by
  induction r generalizing family with
  | zero =>
      have hsub : family ⊆ ({∅} : Finset (Finset α)) := by
        intro S hS
        have hScard : S.card = 0 := huniform S hS
        have hSempty : S = ∅ := Finset.card_eq_zero.mp hScard
        simpa [hSempty]
      calc
        family.card ≤ ({∅} : Finset (Finset α)).card :=
          Finset.card_le_card hsub
        _ = (k - 1) ^ 0 * Nat.factorial 0 := by simp
  | succ r ih =>
      have hr : 1 ≤ r + 1 := by omega
      have huniform' : ∀ S ∈ family, S.card = r + 1 := by
        simpa [Nat.succ_eq_add_one] using huniform
      rcases exists_bounded_hitting_set family (r + 1) k hr huniform' hfree with
        ⟨hitting, hhitting_card, hhitting_hits⟩
      let star : α → Finset (Finset α) :=
        fun x => family.filter (fun S => x ∈ S)
      have hcover : family ⊆ hitting.biUnion star := by
        intro S hS
        rcases hhitting_hits S hS with ⟨x, hxH, hxS⟩
        exact Finset.mem_biUnion.mpr
          ⟨x, hxH, Finset.mem_filter.mpr ⟨hS, hxS⟩⟩
      have hstar_bound : ∀ x ∈ hitting,
          (star x).card ≤ (k - 1) ^ r * r.factorial := by
        intro x _hxH
        let reduced : Finset (Finset α) :=
          (star x).image (fun S => S.erase x)
        have hfree_reduced : IsSunflowerFree reduced k := by
          dsimp [reduced, star]
          exact reduction_lemma family k (r + 1) x huniform' hfree
        have huniform_reduced : ∀ T ∈ reduced, T.card = r := by
          intro T hT
          rcases Finset.mem_image.mp hT with ⟨S, hS, hST⟩
          subst T
          have hS' := Finset.mem_filter.mp hS
          rw [Finset.card_erase_of_mem hS'.2, huniform' S hS'.1]
          omega
        have herase_inj : Set.InjOn (fun S : Finset α => S.erase x) (star x) := by
          intro S hS T hT hST
          have hxS : x ∈ S := (Finset.mem_filter.mp hS).2
          have hxT : x ∈ T := (Finset.mem_filter.mp hT).2
          calc
            S = insert x (S.erase x) := (Finset.insert_erase hxS).symm
            _ = insert x (T.erase x) := by
              exact congrArg (insert x) (by simpa only using hST)
            _ = T := Finset.insert_erase hxT
        have hcard_reduced : reduced.card = (star x).card := by
          dsimp [reduced]
          exact Finset.card_image_of_injOn
            (s := star x) (f := fun S : Finset α => S.erase x) herase_inj
        rw [← hcard_reduced]
        exact ih reduced huniform_reduced hfree_reduced
      calc
        family.card ≤ (hitting.biUnion star).card :=
          Finset.card_le_card hcover
        _ ≤ ∑ x ∈ hitting, (star x).card := Finset.card_biUnion_le
        _ ≤ ∑ _x ∈ hitting, ((k - 1) ^ r * r.factorial) := by
          exact Finset.sum_le_sum fun x hx => hstar_bound x hx
        _ = hitting.card * ((k - 1) ^ r * r.factorial) := by simp
        _ ≤ ((r + 1) * (k - 1)) * ((k - 1) ^ r * r.factorial) :=
          Nat.mul_le_mul_right ((k - 1) ^ r * r.factorial) hhitting_card
        _ = (k - 1) ^ (r + 1) * Nat.factorial (r + 1) := by
          rw [Nat.factorial_succ, pow_succ]
          ring

#print axioms exists_pairwiseDisjoint_hitting_subfamily
#print axioms pairwiseDisjoint_card_lt_forbidden
#print axioms exists_bounded_hitting_set
#print axioms erdos_rado_factorial_bound

end Erdos20Classical
