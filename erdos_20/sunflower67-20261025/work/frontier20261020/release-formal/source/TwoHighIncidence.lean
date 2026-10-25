import CompletionMass

namespace FrontierTwoHighIncidence
open Erdos20BCWConditional Erdos20StrictCore Erdos20DegreeCongruences Erdos20Incidence

variable {α : Type*} [DecidableEq α]

/-- Two three-point traces of a four-set overlap in at least two points. -/
theorem common_trace_card_ge_two
    (R U V : Finset α) (hu : R.card = 4)
    (hU : 3 ≤ (R ∩ U).card) (hV : 3 ≤ (R ∩ V).card) :
    2 ≤ (R ∩ (U ∩ V)).card := by
  have h := Finset.card_union_add_card_inter (R ∩ U) (R ∩ V)
  have hs : (R ∩ U) ∪ (R ∩ V) ⊆ R :=
    Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
  have hb := Finset.card_le_card hs
  have he : (R ∩ U) ∩ (R ∩ V) = R ∩ (U ∩ V) := by
    ext v
    simp only [Finset.mem_inter]
    tauto
  rw [he] at h
  omega

/-- General incidence form of the obstruction: a pair of large traces and
stronger degree loss on their overlap force 37 members' units per 126 support
points' units. No sunflower or finite enumeration is assumed here. -/
theorem two_large_traces_incidence_bound
    (H : Finset (Finset α)) (U V : Finset α)
    (hu : ∀ R ∈ H, R.card = 4)
    (hU : ∀ R ∈ H, 3 ≤ (R ∩ U).card)
    (hV : ∀ R ∈ H, 3 ≤ (R ∩ V).card)
    (hdU : ∀ v ∈ U, degree H v ≤ 14)
    (hdUV : ∀ v ∈ U ∩ V, degree H v ≤ 9) :
    37 * H.card ≤ 126 * U.card := by
  have hiU := incidence_sum_eq H U
  have hiUV := incidence_sum_eq H (U ∩ V)
  have hlowU : 3 * H.card ≤ ∑ v ∈ U, degree H v := by
    calc
      3 * H.card = ∑ _R ∈ H, 3 := by simp [Nat.mul_comm]
      _ ≤ ∑ R ∈ H, (R ∩ U).card := Finset.sum_le_sum hU
      _ = _ := hiU
  have hlowUV : 2 * H.card ≤ ∑ v ∈ U ∩ V, degree H v := by
    calc
      2 * H.card = ∑ _R ∈ H, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ R ∈ H, (R ∩ (U ∩ V)).card :=
        Finset.sum_le_sum (fun R hR => common_trace_card_ge_two R U V (hu R hR) (hU R hR) (hV R hR))
      _ = _ := hiUV
  have hcapUV : (∑ v ∈ U ∩ V, degree H v) ≤ 9 * (U ∩ V).card := by
    calc
      _ ≤ ∑ _v ∈ U ∩ V, 9 := Finset.sum_le_sum hdUV
      _ = _ := by simp [Nat.mul_comm]
  have hd : Disjoint (U \ V) (U ∩ V) := by
    apply Finset.disjoint_left.mpr
    intro v hvD hvI
    exact (Finset.mem_sdiff.mp hvD).2 (Finset.mem_inter.mp hvI).2
  have he : (U \ V) ∪ (U ∩ V) = U := by
    ext v
    simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter]
    tauto
  have hpart : (∑ v ∈ U, degree H v) =
      (∑ v ∈ U \ V, degree H v) + ∑ v ∈ U ∩ V, degree H v := by
    rw [← Finset.sum_union hd,he]
  have hcapD : (∑ v ∈ U \ V, degree H v) ≤ 14 * (U \ V).card := by
    calc
      _ ≤ ∑ _v ∈ U \ V, 14 :=
        Finset.sum_le_sum (fun v hv => hdU v (Finset.mem_sdiff.mp hv).1)
      _ = _ := by simp [Nat.mul_comm]
  have hc := Finset.card_sdiff_add_card_inter U V
  omega

/-- For the twelve-point support of a degree-twenty high link, at most forty
residual four-sets can meet both high links in three points under the degree
losses forced by the two disjoint stars. -/
theorem two_large_supports_card_le_forty
    (H : Finset (Finset α)) (U V : Finset α)
    (hu : ∀ R ∈ H, R.card = 4) (hUc : U.card = 12)
    (hU : ∀ R ∈ H, 3 ≤ (R ∩ U).card)
    (hV : ∀ R ∈ H, 3 ≤ (R ∩ V).card)
    (hdU : ∀ v ∈ U, degree H v ≤ 14)
    (hdUV : ∀ v ∈ U ∩ V, degree H v ≤ 9) : H.card ≤ 40 := by
  have h := two_large_traces_incidence_bound H U V hu hU hV hdU hdUV
  rw [hUc] at h
  omega

end FrontierTwoHighIncidence
