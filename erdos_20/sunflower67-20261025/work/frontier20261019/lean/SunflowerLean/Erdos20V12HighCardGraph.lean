import SunflowerLean.Erdos20V12HighCard
import SunflowerLean.Erdos20GraphEquality

namespace Erdos20V12HighCard
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence Erdos20RankThree
open Erdos20GraphEquality

/-- An independent distinguished set meets the support of a triangle in at
most one point. -/
theorem triangle_distinguished_support_le_one {α : Type*} [DecidableEq α]
    (a b c : α) (H : Finset α)
    (hcap : ∀ R ∈ ({{a,b},{a,c},{b,c}} : Finset (Finset α)), (R ∩ H).card≤1) :
    (({a,b,c} : Finset α) ∩ H).card≤1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  obtain ⟨huT,huH⟩ := Finset.mem_inter.mp hu
  obtain ⟨hvT,hvH⟩ := Finset.mem_inter.mp hv
  by_contra huv
  have hp : ({u,v} : Finset α) ∈ ({{a,b},{a,c},{b,c}} : Finset (Finset α)) := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at huT hvT
    rcases huT with rfl | rfl | rfl <;> rcases hvT with rfl | rfl | rfl <;>
      simp_all [Finset.pair_comm]
  have hb := hcap _ hp
  have hsub : ({u,v} : Finset α) ⊆ H := by simp [Finset.insert_subset_iff,huH,hvH]
  rw [Finset.inter_eq_left.mpr hsub] at hb
  have hp2 : ({u,v} : Finset α).card=2 := by simp [huv]
  omega

/-- A distinguished set appearing at most once in every edge of an extremal
six-edge sunflower-free graph has at most two supported points. -/
theorem six_edges_distinguished_support_le_two {α : Type*} [DecidableEq α]
    (K : Finset (Finset α)) (hu : ∀ R ∈ K, R.card=2) (hf : IsSunflowerFree K 3)
    (hc : K.card=6) (H : Finset α) (hcap : ∀ R ∈ K, (R ∩ H).card≤1) :
    (support K ∩ H).card≤2 := by
  obtain ⟨a,b,c,d,e,f,hab,hac,hbc,hde,hdf,hef,hdis,hK⟩ :=
    six_edges_two_disjoint_triangles K hu hf hc
  have hA := triangle_distinguished_support_le_one a b c H (by
    intro R hR; apply hcap R; rw [hK]; exact Finset.mem_union_left _ hR)
  have hB := triangle_distinguished_support_le_one d e f H (by
    intro R hR; apply hcap R; rw [hK]; exact Finset.mem_union_right _ hR)
  have hs : support K = ({a,b,c} : Finset α) ∪ {d,e,f} := by
    rw [hK]
    ext u
    simp only [support, Finset.mem_biUnion, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, id_eq]
    constructor
    · rintro ⟨R, ((rfl | rfl | rfl) | (rfl | rfl | rfl)), huR⟩ <;>
        simp only [Finset.mem_insert, Finset.mem_singleton] at huR <;> tauto
    · rintro ((hua | hub | huc) | (hud | hue | huf))
      · exact ⟨{a,b}, Or.inl (Or.inl rfl), by simp [hua]⟩
      · exact ⟨{a,b}, Or.inl (Or.inl rfl), by simp [hub]⟩
      · exact ⟨{a,c}, Or.inl (Or.inr (Or.inl rfl)), by simp [huc]⟩
      · exact ⟨{d,e}, Or.inr (Or.inl rfl), by simp [hud]⟩
      · exact ⟨{d,e}, Or.inr (Or.inl rfl), by simp [hue]⟩
      · exact ⟨{d,f}, Or.inr (Or.inr (Or.inl rfl)), by simp [huf]⟩
  have hi : support K ∩ H = (({a,b,c} : Finset α) ∩ H) ∪ (({d,e,f} : Finset α) ∩ H) := by
    rw [hs,Finset.union_inter_distrib_right]
  rw [hi]
  exact (Finset.card_union_le _ _).trans (by omega)

/-- Three independent distinguished vertices cannot each have degree two in
a sunflower-free graph. This is a literal edge-family statement. -/
theorem three_independent_degree_two_impossible {α : Type*} [DecidableEq α]
    (K : Finset (Finset α)) (hu : ∀ R ∈ K, R.card=2) (hf : IsSunflowerFree K 3)
    (H : Finset α) (hH : H.card=3) (hcap : ∀ R ∈ K, (R ∩ H).card≤1)
    (hd : ∀ u ∈ H, (K.filter (fun R => u ∈ R)).card=2) : False := by
  classical
  have hlow : 6≤K.card := by
    calc
      _ = ∑ u ∈ H, (K.filter (fun R => u ∈ R)).card := by
        rw [show (∑ u ∈ H, (K.filter (fun R => u ∈ R)).card) = ∑ _u ∈ H, 2 from
          Finset.sum_congr rfl (fun u hu => hd u hu)]
        simp [hH]
      _ = ∑ R ∈ K, (R ∩ H).card := (incidence_sum_eq K H).symm
      _ ≤ ∑ _R ∈ K, 1 := Finset.sum_le_sum hcap
      _ = K.card := by simp
  have hupper := rank_two_three_petals_card_le_six K hu hf
  have hc : K.card=6 := by omega
  have hsub : H ⊆ support K := by
    intro u huH
    obtain ⟨R,hR⟩ := Finset.card_pos.mp (show 0<(K.filter (fun R => u ∈ R)).card by rw [hd u huH]; decide)
    exact member_subset_support (Finset.mem_filter.mp hR).1 (Finset.mem_filter.mp hR).2
  have hsmall := six_edges_distinguished_support_le_two K hu hf hc H hcap
  rw [Finset.inter_eq_right.mpr hsub,hH] at hsmall
  omega

end Erdos20V12HighCard
