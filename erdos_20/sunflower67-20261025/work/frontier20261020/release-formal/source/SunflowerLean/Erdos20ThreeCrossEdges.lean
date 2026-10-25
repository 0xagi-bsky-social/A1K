import SunflowerLean.Erdos20RankFour

/-! Three labeled intersecting edge classes, with no edge in all classes. -/
namespace Erdos20ThreeCrossEdges
open Erdos20CrossBounds Erdos20GraphEquality Erdos20SharpTriples Erdos20Tetrahedron
open Erdos20BCWConditional Erdos20RankThree Erdos20RankFour

/-- An edge meeting every edge of an intersecting three-edge sunflower-free family belongs to it. -/
theorem edge_meets_triangle_mem {α : Type*} [DecidableEq α]
    (G : Finset (Finset α)) (hu : ∀ P ∈ G, P.card = 2) (hf : IsSunflowerFree G 3)
    (hi : ∀ P ∈ G, ∀ Q ∈ G, (P ∩ Q).Nonempty) (hc : G.card = 3)
    (P : Finset α) (hP : P.card = 2) (hh : ∀ Q ∈ G, (P ∩ Q).Nonempty) : P ∈ G := by
  obtain ⟨a,b,c,hab,hac,hbc,hshape⟩ := intersecting_three_edges_triangle G hu
    (fun x => rank_two_three_petals_degree_le_two G hu hf x) hi hc
  obtain ⟨C,hC,hCP⟩ := contains_pair_of_meets_every_pair_of_triple {a,b,c} P
    (by simp [hab,hac,hbc]) (fun C hC => hh C (by rw [hshape]; exact pair_subset_triangle_mem a b c C hC))
  have he : C = P := Finset.eq_of_subset_of_card_le hCP (by rw [hP,(Finset.mem_powersetCard.mp hC).2])
  rw [← he,hshape]
  exact pair_subset_triangle_mem a b c C hC

private theorem sum_le_of_first_three {α : Type*} [DecidableEq α]
    (A B C : Finset (Finset α)) (huA : ∀ P ∈ A, P.card = 2)
    (hfA : IsSunflowerFree A 3) (hiA : ∀ P ∈ A, ∀ Q ∈ A, (P ∩ Q).Nonempty)
    (hA : A.card = 3) (huB : ∀ P ∈ B, P.card = 2) (huC : ∀ P ∈ C, P.card = 2)
    (hAB : ∀ P ∈ A, ∀ Q ∈ B, (P ∩ Q).Nonempty)
    (hAC : ∀ P ∈ A, ∀ Q ∈ C, (P ∩ Q).Nonempty)
    (htr : ∀ P, P ∈ A → P ∈ B → P ∈ C → False) : A.card + B.card + C.card ≤ 6 := by
  have hBA : B ⊆ A := fun P hP => edge_meets_triangle_mem A huA hfA hiA hA P (huB P hP)
    (fun Q hQ => by simpa [Finset.inter_comm] using hAB Q hQ P hP)
  have hCA : C ⊆ A := fun P hP => edge_meets_triangle_mem A huA hfA hiA hA P (huC P hP)
    (fun Q hQ => by simpa [Finset.inter_comm] using hAC Q hQ P hP)
  have hd : Disjoint B C := Finset.disjoint_left.mpr (fun P hB hC => htr P (hBA hB) hB hC)
  have hh := Finset.card_le_card (Finset.union_subset hBA hCA)
  rw [Finset.card_union_of_disjoint hd] at hh
  omega

/-- Three pairwise cross-intersecting graph classes with no common edge have total size at most six. -/
theorem three_edge_classes_sum_le_six {α : Type*} [DecidableEq α]
    (A B C : Finset (Finset α))
    (huA : ∀ P ∈ A, P.card = 2) (hfA : IsSunflowerFree A 3)
    (hiA : ∀ P ∈ A, ∀ Q ∈ A, (P ∩ Q).Nonempty)
    (huB : ∀ P ∈ B, P.card = 2) (hfB : IsSunflowerFree B 3)
    (hiB : ∀ P ∈ B, ∀ Q ∈ B, (P ∩ Q).Nonempty)
    (huC : ∀ P ∈ C, P.card = 2) (hfC : IsSunflowerFree C 3)
    (hiC : ∀ P ∈ C, ∀ Q ∈ C, (P ∩ Q).Nonempty)
    (hAB : ∀ P ∈ A, ∀ Q ∈ B, (P ∩ Q).Nonempty)
    (hAC : ∀ P ∈ A, ∀ Q ∈ C, (P ∩ Q).Nonempty)
    (hBC : ∀ P ∈ B, ∀ Q ∈ C, (P ∩ Q).Nonempty)
    (htr : ∀ P, P ∈ A → P ∈ B → P ∈ C → False) : A.card + B.card + C.card ≤ 6 := by
  have hA := intersecting_rank_two_three_petals_card_le_three A huA hfA hiA
  have hB := intersecting_rank_two_three_petals_card_le_three B huB hfB hiB
  have hC := intersecting_rank_two_three_petals_card_le_three C huC hfC hiC
  by_cases hA3 : A.card = 3
  · exact sum_le_of_first_three A B C huA hfA hiA hA3 huB huC hAB hAC htr
  by_cases hB3 : B.card = 3
  · have hh := sum_le_of_first_three B A C huB hfB hiB hB3 huA huC
      (fun P hP Q hQ => by simpa [Finset.inter_comm] using hAB Q hQ P hP) hBC
      (fun P hP hQ hR => htr P hQ hP hR)
    omega
  by_cases hC3 : C.card = 3
  · have hh := sum_le_of_first_three C A B huC hfC hiC hC3 huA huB
      (fun P hP Q hQ => by simpa [Finset.inter_comm] using hAC Q hQ P hP)
      (fun P hP Q hQ => by simpa [Finset.inter_comm] using hBC Q hQ P hP)
      (fun P hP hQ hR => htr P hQ hR hP)
    omega
  omega

/-- Every exact-trace residual is disjoint from the anchor. -/
theorem residual_exact_trace_disjoint_anchor {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (R C P : Finset α)
    (hP : P ∈ residualLink (exactTrace F R C) C) : Disjoint P R := by
  obtain ⟨S,hS,hCS,hSP⟩ := mem_residualLink_iff.mp hP
  have hi := (Finset.mem_filter.mp hS).2
  apply Finset.disjoint_left.mpr
  intro x hxP hxR
  rw [← hSP] at hxP
  obtain ⟨hxS,hxC⟩ := Finset.mem_sdiff.mp hxP
  apply hxC
  rw [← hi]
  exact Finset.mem_inter.mpr ⟨hxS,hxR⟩

/-- Singleton-trace residuals at the three anchor points have no common edge. -/
theorem no_common_singleton_residual {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hf : IsSunflowerFree F 3) (P : Finset α)
    (ha : P ∈ residualLink (exactTrace F {a,b,c} {a}) {a})
    (hb : P ∈ residualLink (exactTrace F {a,b,c} {b}) {b})
    (hc : P ∈ residualLink (exactTrace F {a,b,c} {c}) {c}) : False := by
  have hd := residual_exact_trace_disjoint_anchor F {a,b,c} {a} P ha
  have haP : a ∉ P := fun h => Finset.disjoint_left.mp hd h (by simp)
  have hbP : b ∉ P := fun h => Finset.disjoint_left.mp hd h (by simp)
  have hcP : c ∉ P := fun h => Finset.disjoint_left.mp hd h (by simp)
  have haF : insert a P ∈ F := by
    have hm : insert a P ∈ exactTrace F {a,b,c} {a} := by simpa using core_union_residual_mem_family ha
    exact (Finset.mem_filter.mp hm).1
  have hbF : insert b P ∈ F := by
    have hm : insert b P ∈ exactTrace F {a,b,c} {b} := by simpa using core_union_residual_mem_family hb
    exact (Finset.mem_filter.mp hm).1
  have hcF : insert c P ∈ F := by
    have hm : insert c P ∈ exactTrace F {a,b,c} {c} := by simpa using core_union_residual_mem_family hc
    exact (Finset.mem_filter.mp hm).1
  have habS : insert a P ≠ insert b P := by
    intro he
    have hm : a ∈ insert b P := he ▸ Finset.mem_insert_self a P
    simp [hab,haP] at hm
  have hacS : insert a P ≠ insert c P := by
    intro he
    have hm : a ∈ insert c P := he ▸ Finset.mem_insert_self a P
    simp [hac,haP] at hm
  have hbcS : insert b P ≠ insert c P := by
    intro he
    have hm : b ∈ insert c P := he ▸ Finset.mem_insert_self b P
    simp [hbc,hbP] at hm
  have habI : insert a P ∩ insert b P = P := by ext x; simp only [Finset.mem_inter,Finset.mem_insert]; aesop
  have hacI : insert a P ∩ insert c P = P := by ext x; simp only [Finset.mem_inter,Finset.mem_insert]; aesop
  have hbcI : insert b P ∩ insert c P = P := by ext x; simp only [Finset.mem_inter,Finset.mem_insert]; aesop
  exact hf {insert a P,insert b P,insert c P}
    (by intro S hS; simp only [Finset.mem_insert,Finset.mem_singleton] at hS; rcases hS with rfl | rfl | rfl <;> assumption)
    (sunflower_three_of_intersections _ _ _ P habS hacS hbcS habI hacI hbcI)

/-- At most six members of an intersecting sunflower-free triple family meet an anchor in one point. -/
theorem intersecting_triple_singleton_sum_le_six {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hR : {a,b,c} ∈ F) (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) :
    (exactTrace F {a,b,c} {a}).card + (exactTrace F {a,b,c} {b}).card +
      (exactTrace F {a,b,c} {c}).card ≤ 6 := by
  let G := fun x => residualLink (exactTrace F {a,b,c} {x}) {x}
  have hg : ∀ x, ∀ P ∈ G x, P.card = 2 := by
    intro x
    simpa [G] using residualLink_uniform (core := {x}) (fun S hS => hu S (Finset.mem_filter.mp hS).1)
  have hfree : ∀ x, IsSunflowerFree (G x) 3 := fun x => exact_trace_residual_free F {a,b,c} {x} 3 hf
  have hint : ∀ x, ∀ P ∈ G x, ∀ Q ∈ G x, (P ∩ Q).Nonempty := fun x =>
    exact_trace_residual_intersecting F {a,b,c} {x} 3 hR hu hf (by simp)
  have hcross : ∀ x y, x ≠ y → ∀ P ∈ G x, ∀ Q ∈ G y, (P ∩ Q).Nonempty := by
    intro x y hxy
    exact disjoint_traces_residual_cross_intersect F {a,b,c} {x} {y} hi (by simp [Ne.symm hxy])
  have hh := three_edge_classes_sum_le_six (G a) (G b) (G c)
    (hg a) (hfree a) (hint a) (hg b) (hfree b) (hint b) (hg c) (hfree c) (hint c)
    (hcross a b hab) (hcross a c hac) (hcross b c hbc)
    (no_common_singleton_residual F a b c hab hac hbc hf)
  simpa [G,exact_trace_card_residual] using hh

end Erdos20ThreeCrossEdges
