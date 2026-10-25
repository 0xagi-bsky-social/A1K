import SunflowerLean.Erdos20V12HighCard

namespace Erdos20V12HighCard
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20ExtremalTwenty

/-- Three binary classifications of more than eight points share a class
on some pair of distinct points. -/
theorem three_binary_classes_shared_pair {α : Type*} [DecidableEq α]
    (N A B C : Finset α) (hN : 8<N.card) :
    ∃ u ∈ N, ∃ v ∈ N, u≠v ∧ (u∈A ↔ v∈A) ∧ (u∈B ↔ v∈B) ∧ (u∈C ↔ v∈C) := by
  classical
  let code : α → Bool × Bool × Bool := fun u => (decide (u∈A),decide (u∈B),decide (u∈C))
  have hc : (Finset.univ : Finset (Bool × Bool × Bool)).card < N.card := by
    simpa using hN
  obtain ⟨u,hu,v,hv,huv,he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc
    (show Set.MapsTo code N (Finset.univ : Finset (Bool × Bool × Bool)) from by intro u hu; simpa using (Finset.mem_univ (code u)))
  have hA := congrArg Prod.fst he
  have hB := congrArg (fun p : Bool × Bool × Bool => p.2.1) he
  have hC := congrArg (fun p : Bool × Bool × Bool => p.2.2) he
  refine ⟨u,hu,v,hv,huv,?_,?_,?_⟩
  · by_cases huA : u∈A <;> by_cases hvA : v∈A <;> simp_all [code]
  · by_cases huB : u∈B <;> by_cases hvB : v∈B <;> simp_all [code]
  · by_cases huC : u∈C <;> by_cases hvC : v∈C <;> simp_all [code]

/-- The two ten-components of an extremal link define a binary classification
such that any two distinct support points of the same class occur together. -/
theorem twenty_link_binary_pair_classification {α : Type*} [DecidableEq α]
    (L : Finset (Finset α)) (hu : ∀ P ∈ L, P.card=3)
    (hf : IsSunflowerFree L 3) (hc : L.card=20) :
    ∃ S : Finset α, ∀ u ∈ support L, ∀ v ∈ support L,
      u≠v → (u∈S ↔ v∈S) → ∃ P ∈ L, u∈P ∧ v∈P := by
  obtain ⟨A,B,hL,hdis,hpars⟩ := extremal_twenty_two_disjoint_designs L hu hf hc
  refine ⟨support A,?_⟩
  intro u huL v hvL huv he
  have exists_pair (D : Finset (Finset α)) (hDL : D ⊆ L)
      (hp : ∀ u ∈ support D, ∀ v ∈ support D, u≠v →
        (D.filter (fun P => ({u,v} : Finset α) ⊆ P)).card=2)
      (huD : u∈support D) (hvD : v∈support D) : ∃ P∈L, u∈P ∧ v∈P := by
    obtain ⟨P,hP⟩ := Finset.card_pos.mp (show 0<(D.filter (fun P => ({u,v} : Finset α) ⊆ P)).card by
      rw [hp u huD v hvD huv]; decide)
    obtain ⟨hPD,hpair⟩ := Finset.mem_filter.mp hP
    exact ⟨P,hDL hPD,hpair (by simp),hpair (by simp)⟩
  have hAL : A ⊆ L := by rw [hL]; exact Finset.subset_union_left
  have hBL : B ⊆ L := by rw [hL]; exact Finset.subset_union_right
  by_cases huA : u∈support A
  · exact exists_pair A hAL (hpars A (by simp)).2.2.2.2 huA (he.mp huA)
  · have hvA : v∉support A := fun hvA => huA (he.mpr hvA)
    have inB (w : α) (hwL : w∈support L) (hwA : w∉support A) : w∈support B := by
      obtain ⟨P,hP,hwP⟩ := Finset.mem_biUnion.mp hwL
      rw [hL] at hP
      rcases Finset.mem_union.mp hP with hPA | hPB
      · exact False.elim (hwA (member_subset_support hPA hwP))
      · exact member_subset_support hPB hwP
    exact exists_pair B hBL (hpars B (by simp)).2.2.2.2 (inB u huL huA) (inB v hvL hvA)

/-- Three extremal twenty-triple families on one twelve-point support have a
pair occurring in a block of every family. The proof uses eight binary patterns. -/
theorem three_twenty_links_shared_pair {α : Type*} [DecidableEq α]
    (L M K : Finset (Finset α))
    (huL : ∀ P∈L, P.card=3) (hfL : IsSunflowerFree L 3) (hcL : L.card=20)
    (huM : ∀ P∈M, P.card=3) (hfM : IsSunflowerFree M 3) (hcM : M.card=20)
    (huK : ∀ P∈K, P.card=3) (hfK : IsSunflowerFree K 3) (hcK : K.card=20)
    (heL : support L=support K) (heM : support M=support K) :
    ∃ u∈support K, ∃ v∈support K, u≠v ∧
      (∃ P∈L, u∈P ∧ v∈P) ∧ (∃ P∈M, u∈P ∧ v∈P) ∧ (∃ P∈K, u∈P ∧ v∈P) := by
  obtain ⟨A,hA⟩ := twenty_link_binary_pair_classification L huL hfL hcL
  obtain ⟨B,hB⟩ := twenty_link_binary_pair_classification M huM hfM hcM
  obtain ⟨C,hC⟩ := twenty_link_binary_pair_classification K huK hfK hcK
  have hcS := (extremal_twenty_regular_twelve K huK hfK hcK).1
  obtain ⟨u,hu,v,hv,huv,hua,hub,huc⟩ := three_binary_classes_shared_pair (support K) A B C (by omega)
  exact ⟨u,hu,v,hv,huv,hA u (heL.symm ▸ hu) v (heL.symm ▸ hv) huv hua,
    hB u (heM.symm ▸ hu) v (heM.symm ▸ hv) huv hub,hC u hu v hv huv huc⟩

end Erdos20V12HighCard
