import TwoStarResidual
import SunflowerLean.Erdos20V11HighSupport

namespace FrontierTwoStarBridge
open Erdos20BCWConditional Erdos20StrictCore Erdos20DegreeCongruences
open Erdos20V8Boundary FrontierTwoStarResidual

variable {α : Type*} [DecidableEq α]

/-- Partition a family into two disjoint point-stars and rows omitting both. -/
theorem two_star_partition (F : Finset (Finset α)) (x y : α)
    (hj : ∀ R ∈ F, ¬ (x ∈ R ∧ y ∈ R)) :
    (F.filter (fun R => x ∉ R ∧ y ∉ R)).card + degree F x + degree F y = F.card := by
  have h1 := Finset.filter_card_add_filter_neg_card_eq_card (s := F) (p := fun R => x ∈ R)
  have h2 := Finset.filter_card_add_filter_neg_card_eq_card
    (s := F.filter (fun R => x ∉ R)) (p := fun R => y ∈ R)
  have he1 : (F.filter (fun R => x ∉ R)).filter (fun R => y ∈ R) = F.filter (fun R => y ∈ R) := by
    ext R
    simp only [Finset.mem_filter]
    constructor
    · tauto
    · rintro ⟨hR,hy⟩
      exact ⟨⟨hR,fun hx => hj R hR ⟨hx,hy⟩⟩,hy⟩
  have he2 : (F.filter (fun R => x ∉ R)).filter (fun R => y ∉ R) =
      F.filter (fun R => x ∉ R ∧ y ∉ R) := by
    ext R
    simp only [Finset.mem_filter]
    tauto
  rw [he1,he2] at h2
  change degree F y + _ = _ at h2
  change degree F x + _ = _ at h1
  omega

/-- The analogous exact partition for the degree at an arbitrary point. -/
theorem two_star_degree_partition (F : Finset (Finset α)) (x y v : α)
    (hj : ∀ R ∈ F, ¬ (x ∈ R ∧ y ∈ R)) :
    degree (F.filter (fun R => x ∉ R ∧ y ∉ R)) v +
      (upperStar F {x,v}).card + (upperStar F {y,v}).card = degree F v := by
  have h := two_star_partition (F.filter (fun R => v ∈ R)) x y
    (fun R hR => hj R (Finset.mem_filter.mp hR).1)
  have he0 : ((F.filter (fun R => v ∈ R)).filter (fun R => x ∉ R ∧ y ∉ R)) =
      (F.filter (fun R => x ∉ R ∧ y ∉ R)).filter (fun R => v ∈ R) := by
    ext R; simp only [Finset.mem_filter]; tauto
  have he (a : α) : degree (F.filter (fun R => v ∈ R)) a = (upperStar F {a,v}).card := by
    unfold degree upperStar
    congr 1
    ext R
    simp only [Finset.mem_filter,Finset.insert_subset_iff,Finset.singleton_subset_iff]
    tauto
  rw [he0,he x,he y] at h
  exact h

/-- Every noncentral supported point of an extremal twenty-link has codegree five. -/
theorem high_pair_codegree (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) (v : α) (hvx : v ≠ x) :
    (upperStar F {x,v}).card = if v ∈ support (residualLink F {x}) then 5 else 0 := by
  have he : ((residualLink F {x}).filter (fun P => v ∈ P)).card = (upperStar F {x,v}).card := by
    simpa [Finset.pair_comm] using card_filter_residualLink F ({x} : Finset α) {v} (by simpa using hvx)
  rw [← he]
  by_cases hv : v ∈ support (residualLink F {x})
  · simp only [hv,if_pos]
    exact (Erdos20ExtremalTwenty.extremal_twenty_regular_twelve _
      (by simpa using residualLink_uniform (core := ({x} : Finset α)) hu)
      (residualLink_sunflowerFree hf)
      (Erdos20V11HighSupport.high_link_twenty_and_support_twelve F hu hf x hx).1).2 v hv
  · simp only [hv,if_false]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro P hP
    exact hv (member_subset_support (Finset.mem_filter.mp hP).1 (Finset.mem_filter.mp hP).2)

/-- The center never lies in its residual-link support. -/
theorem center_outside_link (F : Finset (Finset α)) (x : α) :
    x ∉ support (residualLink F {x}) := by
  intro hx
  obtain ⟨P,hP,hxP⟩ := Finset.mem_biUnion.mp hx
  exact Finset.disjoint_left.mp (residualLink_member_disjoint_core hP) (by simp) hxP

/-- Two omitted independent high stars lower every other degree by five for each link-support membership. -/
theorem residual_degree_bounds (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (x y : α) (hx : x ∈ highPoints F) (hy : y ∈ highPoints F)
    (hj : ∀ R ∈ F, ¬ (x ∈ R ∧ y ∈ R))
    (hd : ∀ v, v ≠ x → v ≠ y → degree F v ≤ 19) :
    (∀ v ∈ support (residualLink F {x}),
      degree (F.filter (fun R => x ∉ R ∧ y ∉ R)) v ≤ 14) ∧
    (∀ v ∈ support (residualLink F {x}) ∩ support (residualLink F {y}),
      degree (F.filter (fun R => x ∉ R ∧ y ∉ R)) v ≤ 9) := by
  have hv (v : α) (hvu : v ∈ support (residualLink F {x})) : v ≠ x ∧ v ≠ y := by
    constructor
    · intro he
      exact center_outside_link F x (he ▸ hvu)
    · intro he
      exact independent_center_outside_link F x y hj (he ▸ hvu)
  constructor
  · intro v hvu
    have he := two_star_degree_partition F x y v hj
    have hp := high_pair_codegree F hu hf x hx v (hv v hvu).1
    rw [if_pos hvu] at hp
    have hmax := hd v (hv v hvu).1 (hv v hvu).2
    omega
  · intro v hvuv
    obtain ⟨hvu,hvv⟩ := Finset.mem_inter.mp hvuv
    have he := two_star_degree_partition F x y v hj
    have hp := high_pair_codegree F hu hf x hx v (hv v hvu).1
    have hq := high_pair_codegree F hu hf y hy v (hv v hvu).2
    rw [if_pos hvu] at hp
    rw [if_pos hvv] at hq
    have hmax := hd v (hv v hvu).1 (hv v hvu).2
    omega

end FrontierTwoStarBridge
