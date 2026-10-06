import SunflowerLean.Erdos20ExtremalStructure
import SunflowerLean.Erdos20MixedCross

/-! Design consequences of six-point, five-regular triple structure. -/
namespace Erdos20DesignConsequences
open Erdos20BCWConditional Erdos20Incidence Erdos20MixedCross

/-- Every supported pair has codegree two in a six-point, five-regular
three-uniform family with no three-petal sunflower. -/
theorem regular_six_pair_codegree_eq_two
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hs : (support F).card = 6)
    (hd : ∀ x ∈ support F, (F.filter (fun S => x ∈ S)).card = 5)
    (x y : α) (hx : x ∈ support F) (hy : y ∈ support F) (hxy : x ≠ y) :
    (F.filter (fun S => ({x,y} : Finset α) ⊆ S)).card = 2 := by
  classical
  let A := F.filter (fun S => x ∈ S)
  let R := (support F).erase x
  have hA : A.card = 5 := hd x hx
  have hR : R.card = 5 := by dsimp [R]; rw [Finset.card_erase_of_mem hx,hs]
  have hyR : y ∈ R := Finset.mem_erase.mpr ⟨Ne.symm hxy,hy⟩
  have hfiber : ∀ z, A.filter (fun S => z ∈ S) = F.filter (fun S => ({x,z} : Finset α) ⊆ S) := by
    intro z
    ext S
    simp [A,Finset.insert_subset_iff,and_assoc]
  have hmeet : ∀ S ∈ A, (S ∩ R).card = 2 := by
    intro S hS
    obtain ⟨hSF,hxS⟩ := Finset.mem_filter.mp hS
    have hsub := member_subset_support hSF
    have he : S ∩ R = S.erase x := by
      ext z
      simp only [Finset.mem_inter,Finset.mem_erase,R]
      exact ⟨fun h => ⟨h.2.1,h.1⟩,fun h => ⟨h.2,h.1,hsub h.2⟩⟩
    rw [he,Finset.card_erase_of_mem hxS,hu S hSF]
  have hsum : (∑ z ∈ R, (A.filter (fun S => z ∈ S)).card) = 10 := by
    rw [← incidence_sum_eq]
    calc
      _ = ∑ _S ∈ A, 2 := Finset.sum_congr rfl hmeet
      _ = 10 := by simp [hA]
  have hbound : ∀ z ∈ R, (A.filter (fun S => z ∈ S)).card ≤ 2 := by
    intro z hz
    rw [hfiber]
    exact triple_pair_degree_le_two F hu hf {x,z}
      (by simp [Ne.symm (Finset.mem_erase.mp hz).1])
  have hybound := hbound y hyR
  have hyeq : (A.filter (fun S => y ∈ S)).card = 2 := by
    by_contra hnot
    have hlt : (∑ z ∈ R, (A.filter (fun S => z ∈ S)).card) < ∑ _z ∈ R, 2 :=
      Finset.sum_lt_sum hbound ⟨y,hyR,by omega⟩
    simp [hsum,hR] at hlt
  simpa [hfiber] using hyeq

/-- The members meeting a supported pair number exactly eight. -/
theorem regular_six_pair_meeting_card_eq_eight
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hs : (support F).card = 6)
    (hd : ∀ x ∈ support F, (F.filter (fun S => x ∈ S)).card = 5)
    (x y : α) (hx : x ∈ support F) (hy : y ∈ support F) (hxy : x ≠ y) :
    (F.filter (fun S => (S ∩ {x,y}).Nonempty)).card = 8 := by
  classical
  let A := F.filter (fun S => x ∈ S)
  let B := F.filter (fun S => y ∈ S)
  have hA : A.card = 5 := hd x hx
  have hB : B.card = 5 := hd y hy
  have heI : A ∩ B = F.filter (fun S => ({x,y} : Finset α) ⊆ S) := by
    ext S
    simp [A,B,Finset.insert_subset_iff,and_assoc,and_left_comm,and_comm]
  have hI : (A ∩ B).card = 2 := by
    rw [heI]
    exact regular_six_pair_codegree_eq_two F hu hf hs hd x y hx hy hxy
  have hU : F.filter (fun S => (S ∩ {x,y}).Nonempty) = A ∪ B := by
    ext S
    simp only [Finset.mem_filter,Finset.mem_union,A,B]
    have he : (S ∩ ({x,y} : Finset α)).Nonempty ↔ x ∈ S ∨ y ∈ S := by
      constructor
      · rintro ⟨a,ha⟩
        obtain ⟨haS,haP⟩ := Finset.mem_inter.mp ha
        simp only [Finset.mem_insert,Finset.mem_singleton] at haP
        rcases haP with he | he
        · exact Or.inl (he ▸ haS)
        · exact Or.inr (he ▸ haS)
      · rintro (hxS | hyS)
        · exact ⟨x,by simp [hxS]⟩
        · exact ⟨y,by simp [hyS]⟩
    rw [he]
    tauto
  rw [hU]
  have hh := Finset.card_union_add_card_inter A B
  omega

/-- A point outside the support lies in no member. -/
theorem degree_eq_zero_of_not_support
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x : α)
    (hx : x ∉ support F) : (F.filter (fun S => x ∈ S)).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  obtain ⟨hSF,hxS⟩ := Finset.mem_filter.mp hS
  exact hx (member_subset_support hSF hxS)

/-- In the regular six-point structure, no two-point set meets all ten members. -/
theorem regular_six_no_two_point_transversal
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hc : F.card = 10) (hs : (support F).card = 6)
    (hd : ∀ x ∈ support F, (F.filter (fun S => x ∈ S)).card = 5)
    (C : Finset α) (hC : C.card = 2) :
    ∃ S ∈ F, S ∩ C = ∅ := by
  classical
  obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp hC
  by_contra hn
  push_neg at hn
  have hhit : ∀ S ∈ F, (S ∩ {x,y}).Nonempty := by
    intro S hS
    exact hn S hS
  have hM : F.filter (fun S => (S ∩ {x,y}).Nonempty) = F := Finset.filter_eq_self.mpr hhit
  by_cases hx : x ∈ support F
  · by_cases hy : y ∈ support F
    · have he := regular_six_pair_meeting_card_eq_eight F hu hf hs hd x y hx hy hxy
      rw [hM,hc] at he
      omega
    · have hxall : ∀ S ∈ F, x ∈ S := by
        intro S hS
        obtain ⟨a,ha⟩ := hhit S hS
        obtain ⟨haS,haC⟩ := Finset.mem_inter.mp ha
        simp only [Finset.mem_insert,Finset.mem_singleton] at haC
        rcases haC with he | he
        · exact he ▸ haS
        · exact False.elim (hy (member_subset_support hS (he ▸ haS)))
      have he : F.filter (fun S => x ∈ S) = F := Finset.filter_eq_self.mpr hxall
      have hh := hd x hx
      rw [he,hc] at hh
      omega
  · have hyall : ∀ S ∈ F, y ∈ S := by
      intro S hS
      obtain ⟨a,ha⟩ := hhit S hS
      obtain ⟨haS,haC⟩ := Finset.mem_inter.mp ha
      simp only [Finset.mem_insert,Finset.mem_singleton] at haC
      rcases haC with he | he
      · exact False.elim (hx (member_subset_support hS (he ▸ haS)))
      · exact he ▸ haS
    obtain ⟨S,hS⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
    have hy : y ∈ support F := member_subset_support hS (hyall S hS)
    have he : F.filter (fun S => y ∈ S) = F := Finset.filter_eq_self.mpr hyall
    have hh := hd y hy
    rw [he,hc] at hh
    omega

end Erdos20DesignConsequences
