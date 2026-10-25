import ProfileAOutside

namespace FrontierTwoStarResidual
open Erdos20BCWConditional Erdos20StrictCore Erdos20ExtremalTransversals
open FrontierProfileAOutside

variable {α : Type*} [DecidableEq α]

/-- A point whose star never meets the other center lies outside that center's link support. -/
theorem independent_center_outside_link
    (F : Finset (Finset α)) (x y : α)
    (hjoint : ∀ R ∈ F, ¬ (x ∈ R ∧ y ∈ R)) :
    y ∉ support (residualLink F {x}) := by
  intro hy
  obtain ⟨P,hP,hyP⟩ := Finset.mem_biUnion.mp hy
  obtain ⟨R,hR,hxR,hRP⟩ := mem_residualLink_iff.mp hP
  apply hjoint R hR
  refine ⟨hxR (by simp),?_⟩
  rw [← hRP] at hyP
  exact (Finset.mem_sdiff.mp hyP).1

/-- A residual member of two independent extremal twenty-stars has at least
three neighbors in the support of either star. The statement is independent
of ambient support size and of a chosen design normal form. -/
theorem residual_meets_link_support_ge_three
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card = 4)
    (hf : IsSunflowerFree F 3) (x y : α)
    (hx20 : (residualLink F {x}).card = 20)
    (hy20 : (residualLink F {y}).card = 20)
    (hjoint : ∀ R ∈ F, ¬ (x ∈ R ∧ y ∈ R))
    (R : Finset α) (hR : R ∈ F) (hxR : x ∉ R) (hyR : y ∉ R) :
    3 ≤ (R ∩ support (residualLink F {x})).card := by
  let U := support (residualLink F {x})
  let O := (insert y R) \ U
  have hyU : y ∉ U := independent_center_outside_link F x y hjoint
  have hyO : y ∈ O := Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self _ _,hyU⟩
  have hOU : Disjoint O U := by
    apply Finset.disjoint_left.mpr
    intro v hvO hvU
    exact (Finset.mem_sdiff.mp hvO).2 hvU
  by_contra hn
  change ¬ 3 ≤ (R ∩ U).card at hn
  have hRO : (R ∩ O).card ≥ 2 := by
    have he : R ∩ O = R \ U := by
      ext v
      simp only [O,Finset.mem_inter,Finset.mem_sdiff,Finset.mem_insert]
      tauto
    have hc := Finset.card_sdiff_add_card_inter R U
    rw [hu R hR] at hc
    rw [he]
    omega
  have hhit : ∀ Q ∈ residualLink F {y}, (Q ∩ R).Nonempty := by
    intro Q hQ
    have hSF : insert y Q ∈ F := by simpa using core_union_residual_mem_family hQ
    have hxS : x ∉ insert y Q := fun hx => hjoint _ hSF ⟨hx,Finset.mem_insert_self _ _⟩
    by_contra hno
    have hRS : Disjoint R (insert y Q) := by
      apply Finset.disjoint_left.mpr
      intro v hvR hvS
      rcases Finset.mem_insert.mp hvS with rfl | hvQ
      · exact hyR hvR
      · exact hno ⟨v,Finset.mem_inter.mpr ⟨hvQ,hvR⟩⟩
    have hSO : 1 ≤ ((insert y Q) ∩ O).card := by
      apply Finset.card_pos.mpr
      exact ⟨y,Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _,hyO⟩⟩
    have hb := disjoint_rows_outside_sum_le_two F hu hf x hx20 O hOU R (insert y Q)
      hR hSF hxR hxS hRS
    omega
  have huY : ∀ Q ∈ residualLink F {y}, Q.card = 3 := by
    simpa using residualLink_uniform (core := ({y} : Finset α)) hu
  have hmin := extremal_twenty_transversal_card_ge_six (residualLink F {y}) huY
    (residualLink_sunflowerFree hf) hy20 R hhit
  rw [hu R hR] at hmin
  omega

end FrontierTwoStarResidual
