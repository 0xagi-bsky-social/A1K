import SunflowerLean.Erdos20V13Boundary

namespace FrontierUniqueDesignTails
open Erdos20BCWConditional Erdos20RankThree

/-- With one single-point extension of a core already present, at most one
other distinct single-point extension is possible in a three-sunflower-free
family. -/
theorem two_other_extensions_equal
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hf : IsSunflowerFree F 3) (T : Finset α) (x a b : α)
    (hx : x ∉ T) (ha : a ∉ T) (hb : b ∉ T)
    (hxa : x ≠ a) (hxb : x ≠ b)
    (hX : insert x T ∈ F) (hA : insert a T ∈ F) (hB : insert b T ∈ F) : a = b := by
  by_contra hab
  have hXA : insert x T ≠ insert a T := by
    intro he
    have hm : x ∈ insert a T := he ▸ Finset.mem_insert_self x T
    simp [hxa,hx] at hm
  have hXB : insert x T ≠ insert b T := by
    intro he
    have hm : x ∈ insert b T := he ▸ Finset.mem_insert_self x T
    simp [hxb,hx] at hm
  have hAB : insert a T ≠ insert b T := by
    intro he
    have hm : a ∈ insert b T := he ▸ Finset.mem_insert_self a T
    simp [hab,ha] at hm
  have inter_shape (u v : α) (huv : u ≠ v) : insert u T ∩ insert v T = T := by
    ext z
    simp only [Finset.mem_inter,Finset.mem_insert]
    aesop
  exact hf {insert x T,insert a T,insert b T}
    (by intro R hR; simp only [Finset.mem_insert,Finset.mem_singleton] at hR
        rcases hR with rfl | rfl | rfl <;> assumption)
    (sunflower_three_of_intersections _ _ _ T hXA hXB hAB
      (inter_shape x a hxa) (inter_shape x b hxb) (inter_shape a b hab))

/-- Projection onto a prescribed design tail is injective among members
with exactly one point outside it, once the center extensions are present. -/
theorem tail_projection_injective
    {α : Type*} [DecidableEq α] (F W : Finset (Finset α))
    (hf : IsSunflowerFree F 3) (hWF : W ⊆ F) (x : α) (B : Finset α)
    (hxB : x ∉ B) (hxW : ∀ R ∈ W, x ∉ R)
    (htail : ∀ R ∈ W, insert x (R ∩ B) ∈ F)
    (hsize : ∀ R ∈ W, (R \ B).card = 1) :
    Set.InjOn (fun R : Finset α => R ∩ B) (↑W : Set (Finset α)) := by
  intro R hR S hS he
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp (hsize R hR)
  obtain ⟨b,hb⟩ := Finset.card_eq_one.mp (hsize S hS)
  have ham : a ∈ R \ B := by rw [ha]; simp
  have hbm : b ∈ S \ B := by rw [hb]; simp
  have hRa : R = insert a (R ∩ B) := by
    ext v
    have h := congrArg (fun T : Finset α => v ∈ T) ha
    simp only [Finset.mem_sdiff,Finset.mem_singleton] at h
    simp only [Finset.mem_insert,Finset.mem_inter]
    have hh := Iff.of_eq h
    tauto
  have hSb : S = insert b (R ∩ B) := by
    have hS' : S = insert b (S ∩ B) := by
      ext v
      have h := congrArg (fun T : Finset α => v ∈ T) hb
      simp only [Finset.mem_sdiff,Finset.mem_singleton] at h
      simp only [Finset.mem_insert,Finset.mem_inter]
      have hh := Iff.of_eq h
      tauto
    simpa only [← he] using hS'
  have hxT : x ∉ R ∩ B := fun h => hxB (Finset.mem_inter.mp h).2
  have haT : a ∉ R ∩ B := fun h => (Finset.mem_sdiff.mp ham).2 (Finset.mem_inter.mp h).2
  have hbT : b ∉ R ∩ B := fun h => (Finset.mem_sdiff.mp hbm).2 (Finset.mem_inter.mp h).2
  have hxa : x ≠ a := by
    intro e
    subst a
    exact hxW R hR (Finset.mem_sdiff.mp ham).1
  have hxb : x ≠ b := by
    intro e
    subst b
    exact hxW S hS (Finset.mem_sdiff.mp hbm).1
  have hab := two_other_extensions_equal F hf (R ∩ B) x a b hxT haT hbT hxa hxb
    (htail R hR) (by rw [← hRa]; exact hWF hR) (by rw [← hSb]; exact hWF hS)
  rw [hRa,hSb,hab]

/-- There are at most ten residual members with one extra point and a tail
belonging to a ten-member design already present at the center. -/
theorem ten_design_tails_card_le_ten
    {α : Type*} [DecidableEq α] (F W K : Finset (Finset α))
    (hf : IsSunflowerFree F 3) (hWF : W ⊆ F) (x : α) (B : Finset α)
    (hxB : x ∉ B) (hxW : ∀ R ∈ W, x ∉ R)
    (hhigh : ∀ T ∈ K, insert x T ∈ F)
    (htail : ∀ R ∈ W, R ∩ B ∈ K)
    (hsize : ∀ R ∈ W, (R \ B).card = 1) (hK : K.card = 10) : W.card ≤ 10 := by
  have hinj := tail_projection_injective F W hf hWF x B hxB hxW
    (fun R hR => hhigh (R ∩ B) (htail R hR)) hsize
  have hsub : W.image (fun R => R ∩ B) ⊆ K := by
    intro T hT
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hT
    exact htail R hR
  have hb := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj,hK] at hb
  exact hb

end FrontierUniqueDesignTails
