import Mathlib.Combinatorics.SimpleGraph.FiveWheelLike
import Mathlib.Tactic

/-! The twenty-vertex equality case of the triangle-free minimum-degree bound.
Only regularity is needed; no full classification of cycle blowups is assumed. -/
namespace Erdos20GraphEqualityEndpoint

open Finset SimpleGraph

def cycleAdjacent (i j : Fin 5) : Prop :=
  (i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val

instance (i j : Fin 5) : Decidable (cycleAdjacent i j) := by
  unfold cycleAdjacent
  infer_instance

def independentProfile (S : Finset (Fin 5)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, ¬ cycleAdjacent i j

instance (S : Finset (Fin 5)) : Decidable (independentProfile S) := by
  unfold independentProfile
  infer_instance

theorem independentProfile_card_le_two :
    ∀ S : Finset (Fin 5), independentProfile S → S.card ≤ 2 := by decide

theorem independent_pair_is_cycle_neighborhood :
    ∀ S : Finset (Fin 5), independentProfile S → S.card = 2 →
      ∃ v : Fin 5, ∀ i, i ∈ S ↔ cycleAdjacent v i := by decide

theorem independent_pair_disjoint_neighborhood_contains_center :
    ∀ (v : Fin 5) (T : Finset (Fin 5)), independentProfile T → T.card = 2 →
      (∀ i ∈ T, ¬ cycleAdjacent v i) → v ∈ T := by decide

variable {α : Type*} [Fintype α] [DecidableEq α]

def profile (G : SimpleGraph α) [DecidableRel G.Adj]
    (e : Fin 5 → α) (x : α) : Finset (Fin 5) :=
  univ.filter (fun i => G.Adj x (e i))

omit [Fintype α] in
theorem profile_independent (G : SimpleGraph α) [DecidableRel G.Adj]
    (hf : G.CliqueFree 3) (e : Fin 5 → α)
    (he : ∀ i j, cycleAdjacent i j → G.Adj (e i) (e j)) (x : α) :
    independentProfile (profile G e x) := by
  intro i hi j hj hij
  have hxi : G.Adj x (e i) := (mem_filter.mp hi).2
  have hxj : G.Adj x (e j) := (mem_filter.mp hj).2
  apply hf {e i, e j, x}
  exact is3Clique_iff.mpr ⟨e i, e j, x, he i j hij, hxi.symm, hxj.symm, rfl⟩

omit [DecidableEq α] in
theorem sum_cycle_degrees_eq_sum_profiles (G : SimpleGraph α) [DecidableRel G.Adj]
    (e : Fin 5 → α) :
    (∑ i : Fin 5, G.degree (e i)) = ∑ x : α, (profile G e x).card := by
  simp only [SimpleGraph.degree, neighborFinset_eq_filter, profile, card_eq_sum_ones]
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro i _
  simp only [adj_comm]

/-- A five-cycle and the equality threshold force every profile to have two
neighbors and every cycle vertex to have degree eight. -/
theorem profile_saturation (G : SimpleGraph α) [DecidableRel G.Adj]
    (hn : Fintype.card α = 20) (hf : G.CliqueFree 3)
    (hd : ∀ x, 8 ≤ G.degree x) (e : Fin 5 → α)
    (he : ∀ i j, cycleAdjacent i j → G.Adj (e i) (e j)) :
    (∀ x, (profile G e x).card = 2) ∧ (∀ i, G.degree (e i) = 8) := by
  have hp : ∀ x, (profile G e x).card ≤ 2 := fun x =>
    independentProfile_card_le_two _ (profile_independent G hf e he x)
  have hsum := sum_cycle_degrees_eq_sum_profiles G e
  have hlo : 40 ≤ ∑ i : Fin 5, G.degree (e i) := by
    calc
      _ = ∑ _i : Fin 5, 8 := by simp
      _ ≤ _ := sum_le_sum (fun i _ => hd (e i))
  have hhi : (∑ x : α, (profile G e x).card) ≤ 40 := by
    calc
      _ ≤ ∑ _x : α, 2 := sum_le_sum (fun x _ => hp x)
      _ = _ := by simp [hn]
  have hsum40 : (∑ x : α, (profile G e x).card) = 40 := by omega
  constructor
  · intro x
    by_contra hx
    have hl : (∑ y : α, (profile G e y).card) < ∑ _y : α, 2 :=
      sum_lt_sum (fun y _ => hp y) ⟨x, mem_univ _, by have := hp x; omega⟩
    simp [hn, hsum40] at hl
  · intro i
    by_contra hi
    have hl : (∑ _j : Fin 5, 8) < ∑ j : Fin 5, G.degree (e j) :=
      sum_lt_sum (fun j _ => hd (e j)) ⟨i, mem_univ _, by have := hd (e i); omega⟩
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hl
    omega

/-- Every vertex has its neighborhood contained in that of one cycle vertex. -/
theorem neighborhood_contained_in_cycle_neighborhood
    (G : SimpleGraph α) [DecidableRel G.Adj] (hf : G.CliqueFree 3)
    (e : Fin 5 → α) (he : ∀ i j, cycleAdjacent i j → G.Adj (e i) (e j))
    (hp : ∀ x, (profile G e x).card = 2) (x : α) :
    ∃ i : Fin 5, G.neighborFinset x ⊆ G.neighborFinset (e i) := by
  obtain ⟨i, hi⟩ := independent_pair_is_cycle_neighborhood (profile G e x)
    (profile_independent G hf e he x) (hp x)
  refine ⟨i, ?_⟩
  intro y hy
  have hxy : G.Adj x y := by simpa only [mem_neighborFinset] using hy
  have hit : i ∈ profile G e y := by
    apply independent_pair_disjoint_neighborhood_contains_center i (profile G e y)
      (profile_independent G hf e he y) (hp y)
    intro j hj hij
    have hxj : G.Adj x (e j) := (mem_filter.mp ((hi j).mpr hij)).2
    have hyj : G.Adj y (e j) := (mem_filter.mp hj).2
    apply hf {x,y,e j}
    exact is3Clique_iff.mpr ⟨x,y,e j,hxy,hxj,hyj,rfl⟩
  simpa only [mem_neighborFinset] using (mem_filter.mp hit).2.symm

theorem regular_of_cycle_at_threshold
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hn : Fintype.card α = 20) (hf : G.CliqueFree 3)
    (hd : ∀ x, 8 ≤ G.degree x) (e : Fin 5 → α)
    (he : ∀ i j, cycleAdjacent i j → G.Adj (e i) (e j)) :
    ∀ x, G.degree x = 8 := by
  obtain ⟨hp, hc⟩ := profile_saturation G hn hf hd e he
  intro x
  obtain ⟨i, hi⟩ := neighborhood_contained_in_cycle_neighborhood G hf e he hp x
  have hu : G.degree x ≤ G.degree (e i) := card_le_card hi
  have hl := hd x
  rw [hc i] at hu
  omega

omit [Fintype α] in
/-- A wheel with singleton sides supplies the five cycle edges needed above. -/
theorem five_cycle_of_wheel (G : SimpleGraph α)
    {k : ℕ} {v w₁ w₂ : α} {s t : Finset α}
    (hw : G.IsFiveWheelLike 1 k v w₁ w₂ s t) :
    ∃ e : Fin 5 → α, ∀ i j, cycleAdjacent i j → G.Adj (e i) (e j) := by
  obtain ⟨a, ha⟩ := card_eq_one.mp hw.card_left
  obtain ⟨b, hb⟩ := card_eq_one.mp hw.card_right
  have hva : v ≠ a := by simpa [ha] using hw.notMem_left
  have hvb : v ≠ b := by simpa [hb] using hw.notMem_right
  have hwa : w₁ ≠ a := by simpa [ha] using hw.fst_notMem
  have hwb : w₂ ≠ b := by simpa [hb] using hw.snd_notMem
  have h01 : G.Adj v a := hw.isNClique_left.1 (by simp) (by simp [ha]) hva
  have h12 : G.Adj a w₁ := (hw.isNClique_fst_left.1 (by simp) (by simp [ha]) hwa).symm
  have h23 : G.Adj w₁ w₂ := hw.isPathGraph3Compl.adj
  have h34 : G.Adj w₂ b := hw.isNClique_snd_right.1 (by simp) (by simp [hb]) hwb
  have h40 : G.Adj b v := (hw.isNClique_right.1 (by simp) (by simp [hb]) hvb).symm
  let e : Fin 5 → α := ![v,a,w₁,w₂,b]
  refine ⟨e, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [cycleAdjacent, e, h01, h12, h23, h34, h40,
      h01.symm, h12.symm, h23.symm, h34.symm, h40.symm] at hij ⊢

/-- Equality-case regularity at twenty vertices. A full blowup classification
is not needed: the maximal triangle-free supergraph is already eight-regular. -/
theorem twenty_vertex_nonbipartite_regular
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (hn : Fintype.card α = 20) (hf : G.CliqueFree 3)
    (hd : ∀ x, 8 ≤ G.degree x) (hnot : ¬ G.Colorable 2) :
    ∀ x, G.degree x = 8 := by
  classical
  obtain ⟨H, hGH, hmax⟩ := @Finite.exists_le_maximal _ _ _
    (fun H : SimpleGraph α => H.CliqueFree 3) G hf
  have hnc : ¬ H.IsCompleteMultipartite := by
    intro h
    exact hnot ((h.colorable_of_cliqueFree hmax.1).mono_left hGH)
  obtain ⟨v,w₁,w₂,s,t,hw⟩ :=
    exists_isFiveWheelLike_of_maximal_cliqueFree_not_isCompleteMultipartite
      (r := 1) hmax hnc
  obtain ⟨e,he⟩ := five_cycle_of_wheel H hw
  have hdeg : ∀ x, G.degree x ≤ H.degree x := by
    intro x
    apply card_le_card
    intro y hy
    have ha : G.Adj x y := by simpa only [mem_neighborFinset] using hy
    simpa only [mem_neighborFinset] using hGH ha
  have hH := regular_of_cycle_at_threshold H hn hmax.1
    (fun x => (hd x).trans (hdeg x)) e he
  intro x
  have hu := hdeg x
  rw [hH x] at hu
  have hl := hd x
  omega

end Erdos20GraphEqualityEndpoint
