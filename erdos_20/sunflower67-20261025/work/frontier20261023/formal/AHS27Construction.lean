import AHS27Data

namespace FrontierAHS27

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Direct construction: an unordered choice of two different groups, followed
by two-element subsets of each selected group. -/
def chooseTwoGroups : Finset (Finset (Fin 9)) :=
  ((Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun ij => ij.1 < ij.2)).biUnion
    (fun ij => ((group ij.1).powersetCard 2).biUnion
      (fun P => ((group ij.2).powersetCard 2).image (fun Q => P ∪ Q)))

/-- The literal block table is exactly the stated pair-of-pairs construction. -/
theorem AHS_eq_chooseTwoGroups : AHS = chooseTwoGroups := by decide +kernel

theorem group_card : ∀ i : Fin 3, (group i).card = 3 := by decide +kernel

theorem groups_disjoint : ∀ i j : Fin 3, i ≠ j → Disjoint (group i) (group j) := by
  decide +kernel

theorem groups_cover : (Finset.univ.biUnion group) = Finset.univ := by decide +kernel

theorem AHS_support : Erdos20BCWConditional.support AHS = Finset.univ := by
  decide +kernel

end FrontierAHS27
