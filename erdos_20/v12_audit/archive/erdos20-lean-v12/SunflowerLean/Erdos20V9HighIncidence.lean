import SunflowerLean.Erdos20V8HighWeights

namespace Erdos20V9HighIncidence
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20V8DesignCounts Erdos20V8Boundary Erdos20DegreeCongruences
open Erdos20V8HighWeights Erdos20ExtremalTwenty

/-- A ten-design cannot contain two distinguished supported points if no block
contains two of them: every supported pair belongs to exactly two blocks. -/
theorem ten_design_distinguished_support_card_le_one
    {α : Type*} [DecidableEq α] (A : Finset (Finset α))
    (hu : ∀ P ∈ A, P.card = 3) (hf : IsSunflowerFree A 3)
    (hi : ∀ P ∈ A, ∀ Q ∈ A, (P ∩ Q).Nonempty) (hc : A.card = 10)
    (H : Finset α) (hcap : ∀ P ∈ A, (P ∩ H).card ≤ 1) :
    (support A ∩ H).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  have hpair := (Erdos20V5Frontier.intersecting_ten_design A hu hf hi hc).2.2
    x (Finset.mem_inter.mp hx).1 y (Finset.mem_inter.mp hy).1 hxy
  obtain ⟨P,hP⟩ := Finset.card_pos.mp (show 0 < (A.filter (fun P => ({x,y} : Finset α) ⊆ P)).card by omega)
  obtain ⟨hPA,hxyP⟩ := Finset.mem_filter.mp hP
  have hsub : ({x,y} : Finset α) ⊆ P ∩ H := by
    intro t ht
    refine Finset.mem_inter.mpr ⟨hxyP ht,?_⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact (Finset.mem_inter.mp hx).2
    · exact (Finset.mem_inter.mp hy).2
  have hh := Finset.card_le_card hsub
  have h2 : ({x,y} : Finset α).card = 2 := by simp [hxy]
  have := hcap P hPA
  omega

/-- A twenty-triple link with at most one distinguished point per block has
at most two distinguished supported points. -/
theorem twenty_link_distinguished_support_card_le_two
    {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hu : ∀ P ∈ L, P.card = 3) (hf : IsSunflowerFree L 3) (hc : L.card = 20)
    (H : Finset α) (hcap : ∀ P ∈ L, (P ∩ H).card ≤ 1) :
    (support L ∩ H).card ≤ 2 := by
  obtain ⟨A,B,hL,hdis,hpars⟩ := extremal_twenty_two_disjoint_designs L hu hf hc
  have hAL : A ⊆ L := by rw [hL]; exact Finset.subset_union_left
  have hBL : B ⊆ L := by rw [hL]; exact Finset.subset_union_right
  have ha := hpars A (by simp)
  have hb := hpars B (by simp)
  have hAcap := ten_design_distinguished_support_card_le_one A (fun P hP => hu P (hAL hP))
    (fun C hC hs => hf C (hC.trans hAL) hs) ha.2.1 ha.1 H (fun P hP => hcap P (hAL hP))
  have hBcap := ten_design_distinguished_support_card_le_one B (fun P hP => hu P (hBL hP))
    (fun C hC hs => hf C (hC.trans hBL) hs) hb.2.1 hb.1 H (fun P hP => hcap P (hBL hP))
  have he : support L ∩ H = (support A ∩ H) ∪ (support B ∩ H) := by
    rw [hL]
    ext x
    simp only [support,Finset.mem_inter,Finset.mem_union,Finset.mem_biUnion]
    aesop
  rw [he]
  exact (Finset.card_union_le _ _).trans (by omega)

/-- An extremal link meets a fixed nondistinguished point and the distinguished
set in at most two blocks. -/
theorem twenty_link_point_distinguished_card_le_two
    {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hu : ∀ P ∈ L, P.card = 3) (hf : IsSunflowerFree L 3) (hc : L.card = 20)
    (H : Finset α) (hcap : ∀ P ∈ L, (P ∩ H).card ≤ 1)
    (x : α) (hxH : x ∉ H) :
    (L.filter (fun P => x ∈ P ∧ (P ∩ H).Nonempty)).card ≤ 2 := by
  classical
  let D := L.filter (fun P => x ∈ P ∧ (P ∩ H).Nonempty)
  by_cases hD : D.Nonempty
  · obtain ⟨P,hP⟩ := hD
    obtain ⟨hPL,hxP,z,hz⟩ := Finset.mem_filter.mp hP
    obtain ⟨hzP,hzH⟩ := Finset.mem_inter.mp hz
    obtain ⟨A,B,hL,hdis,hpars⟩ := extremal_twenty_two_disjoint_designs L hu hf hc
    have hAL : A ⊆ L := by rw [hL]; exact Finset.subset_union_left
    have hBL : B ⊆ L := by rw [hL]; exact Finset.subset_union_right
    have one_component (A B : Finset (Finset α)) (hL : L=A∪B)
        (hdis : Disjoint (support A) (support B)) (hAL : A ⊆ L)
        (hAc : A.card=10) (hAi : ∀ Q ∈ A, ∀ R ∈ A, (Q∩R).Nonempty) (hPA : P ∈ A) : D.card ≤ 2 := by
      have hcapA := ten_design_distinguished_support_card_le_one A (fun Q hQ => hu Q (hAL hQ))
        (fun C hC hs => hf C (hC.trans hAL) hs) hAi hAc H (fun Q hQ => hcap Q (hAL hQ))
      have hzA : z ∈ support A ∩ H := Finset.mem_inter.mpr ⟨member_subset_support hPA hzP,hzH⟩
      have hsub : D ⊆ A.filter (fun Q => ({x,z} : Finset α) ⊆ Q) := by
        intro Q hQ
        obtain ⟨hQL,hxQ,w,hw⟩ := Finset.mem_filter.mp hQ
        obtain ⟨hwQ,hwH⟩ := Finset.mem_inter.mp hw
        have hQA : Q ∈ A := by
          rw [hL] at hQL
          rcases Finset.mem_union.mp hQL with h | h
          · exact h
          · exact False.elim (Finset.disjoint_left.mp hdis (member_subset_support hPA hxP) (member_subset_support h hxQ))
        have hwA : w ∈ support A ∩ H := Finset.mem_inter.mpr ⟨member_subset_support hQA hwQ,hwH⟩
        have hwz : w=z := Finset.card_le_one.mp hcapA w hwA z hzA
        apply Finset.mem_filter.mpr
        refine ⟨hQA,?_⟩
        simpa [Finset.insert_subset_iff,hwz] using And.intro hxQ (And.intro hwQ (show (∅ : Finset α) ⊆ Q from Finset.empty_subset Q))
      have hpair := (Erdos20V5Frontier.intersecting_ten_design A (fun Q hQ => hu Q (hAL hQ))
        (fun C hC hs => hf C (hC.trans hAL) hs) hAi hAc).2.2
        x (member_subset_support hPA hxP) z (member_subset_support hPA hzP) (fun he => hxH (he ▸ hzH))
      exact (Finset.card_le_card hsub).trans hpair.le
    rw [hL] at hPL
    rcases Finset.mem_union.mp hPL with hPA | hPB
    · exact one_component A B hL hdis hAL (hpars A (by simp)).1 (hpars A (by simp)).2.1 hPA
    · exact one_component B A (by rw [hL,Finset.union_comm]) hdis.symm hBL
        (hpars B (by simp)).1 (hpars B (by simp)).2.1 hPB
  · have he : D=∅ := Finset.not_nonempty_iff_eq_empty.mp hD
    change D.card ≤ 2
    simp [he]

/-- Double incidences cannot conceal more than one fifth of the contribution
of a collection of degree-five distinguished points. -/
theorem degree_five_distinguished_count
    {α : Type*} [DecidableEq α] (G : Finset (Finset α)) (H : Finset α)
    (hcap : ∀ R ∈ G, (R ∩ H).card ≤ 2)
    (hdegree : ∀ x ∈ H, (G.filter (fun R => x ∈ R)).card = 5)
    (hdouble : ∀ x ∈ H,
      ((G.filter (fun R => (R ∩ H).card = 2)).filter (fun R => x ∈ R)).card ≤ 2) :
    4 * H.card ≤ G.card := by
  classical
  let D := G.filter (fun R => (R ∩ H).card = 2)
  have hD : 2*D.card ≤ 2*H.card := by
    calc
      _ = ∑ R ∈ D, (R ∩ H).card := by
        rw [show (∑ R ∈ D, (R ∩ H).card) = ∑ _R ∈ D, 2 from
          Finset.sum_congr rfl (fun R hR => (Finset.mem_filter.mp hR).2)]
        simp [Nat.mul_comm]
      _ = ∑ x ∈ H, (D.filter (fun R => x ∈ R)).card := incidence_sum_eq D H
      _ ≤ ∑ _x ∈ H, 2 := Finset.sum_le_sum (fun x hx => hdouble x hx)
      _ = _ := by simp [Nat.mul_comm]
  have htotal : (∑ R ∈ G, (R ∩ H).card) = 5*H.card := by
    rw [incidence_sum_eq]
    calc
      _ = ∑ _x ∈ H, 5 := Finset.sum_congr rfl (fun x hx => hdegree x hx)
      _ = _ := by simp [Nat.mul_comm]
  have hbound : (∑ R ∈ G, (R ∩ H).card) ≤ G.card+D.card := by
    calc
      _ ≤ ∑ R ∈ G, (1 + if (R ∩ H).card=2 then 1 else 0) := by
        apply Finset.sum_le_sum
        intro R hR
        have := hcap R hR
        split_ifs <;> omega
      _ = _ := by
        simp only [Finset.sum_add_distrib,Finset.sum_const,Nat.nsmul_eq_mul,mul_one]
        rw [← Finset.card_filter]
  omega

end Erdos20V9HighIncidence
