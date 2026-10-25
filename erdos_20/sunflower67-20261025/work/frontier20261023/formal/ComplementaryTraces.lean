import TerminalSeparation

/-!
The exceptional-trace obstruction used in the P9 complement argument.
This is stated for actual finite sets on an arbitrary ground type. It does
not assume a classification, bound the ambient support, or import H27.
-/
namespace FrontierTerminal

universe u
variable {α : Type u} [DecidableEq α]

set_option maxHeartbeats 800000

theorem lifted_disjoint_intersection
    (B U : Finset α) (x z : α)
    (hBU : Disjoint B U) (hxB : x ∉ B) (hzU : z ∈ U) :
    insert z B ∩ insert x U = {z} := by
  ext a
  constructor
  · intro ha
    obtain ⟨haB, haU⟩ := Finset.mem_inter.mp ha
    rcases Finset.mem_insert.mp haB with rfl | haB
    · simp
    · rcases Finset.mem_insert.mp haU with rfl | haU
      · exact False.elim (hxB haB)
      · exact False.elim (Finset.disjoint_left.mp hBU haB haU)
  · intro ha
    have haz : a = z := Finset.mem_singleton.mp ha
    subst a
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hzU⟩

/-- Two disjoint nonempty traces at the same exterior centre cannot coexist
with an actual outside cone containing that centre. -/
theorem no_two_disjoint_traces_with_surviving_cone
    (F : Finset (Finset α)) (B C U : Finset α) (x z : α)
    (hf : IsSunflowerFree F 3)
    (hB : B.Nonempty) (hBC : Disjoint B C)
    (hBU : Disjoint B U) (hCU : Disjoint C U)
    (hxB : x ∉ B) (hxC : x ∉ C) (hzB : z ∉ B)
    (hxz : x ≠ z) (hzU : z ∈ U)
    (hFB : insert z B ∈ F) (hFC : insert z C ∈ F)
    (hFU : insert x U ∈ F) : False := by
  have hneqBC : insert z B ≠ insert z C := by
    intro heq
    obtain ⟨b, hb⟩ := hB
    have hbC : b ∈ insert z C := by
      rw [← heq]
      exact Finset.mem_insert_of_mem hb
    rcases Finset.mem_insert.mp hbC with rfl | hbC
    · exact hzB hb
    · exact Finset.disjoint_left.mp hBC hb hbC
  have hxnotB : x ∉ insert z B := by simp [hxz, hxB]
  have hxnotC : x ∉ insert z C := by simp [hxz, hxC]
  have hneqBU : insert z B ≠ insert x U := by
    intro heq
    apply hxnotB
    rw [heq]
    exact Finset.mem_insert_self _ _
  have hneqCU : insert z C ≠ insert x U := by
    intro heq
    apply hxnotC
    rw [heq]
    exact Finset.mem_insert_self _ _
  have hBCint : insert z B ∩ insert z C = {z} := by
    ext a
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨ha | ha, hb | hb⟩
      · exact ha
      · exact ha
      · exact hb
      · exact False.elim (Finset.disjoint_left.mp hBC ha hb)
    · intro ha
      exact ⟨Or.inl ha, Or.inl ha⟩
  apply hf {insert z B, insert z C, insert x U}
  · intro A hA
    simp only [Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl
    · exact hFB
    · exact hFC
    · exact hFU
  · exact Erdos20RankThree.sunflower_three_of_intersections
      (insert z B) (insert z C) (insert x U) {z}
      hneqBC hneqBU hneqCU hBCint
      (lifted_disjoint_intersection B U x z hBU hxB hzU)
      (lifted_disjoint_intersection C U x z hCU hxC hzU)

#print axioms lifted_disjoint_intersection
#print axioms no_two_disjoint_traces_with_surviving_cone

end FrontierTerminal
