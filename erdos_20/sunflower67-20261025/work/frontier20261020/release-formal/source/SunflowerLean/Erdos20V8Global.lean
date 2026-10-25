import SunflowerLean.Erdos20V7Bounds
import SunflowerLean.Erdos20ExtremalTransversals

/-! Degree-sensitive reductions for the unrestricted rank-four problem.
The target upper bound82 remains conditional on a degree cap in this module. -/
namespace Erdos20V8Global
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20RankThree Erdos20RankFour Erdos20SharpTriples Erdos20FortyOne
open Erdos20ExtremalTwenty Erdos20DesignSeparation

/-- In a split family, the members disjoint from an anchor are exactly the other component. -/
theorem disjoint_trace_eq_other_component
    {α : Type*} [DecidableEq α] (H K : Finset (Finset α))
    (hi : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty)
    (hd : Disjoint (support H) (support K)) (A : Finset α) (hA : A ∈ H) :
    exactTrace (H ∪ K) A ∅ = K := by
  classical
  ext B
  simp only [exactTrace,Finset.mem_filter,Finset.mem_union]
  constructor
  · rintro ⟨hB,hBA⟩
    rcases hB with hB | hB
    · have hh := hi B hB A hA
      rw [hBA] at hh
      exact False.elim (Finset.not_nonempty_empty hh)
    · exact hB
  · intro hB
    refine ⟨Or.inr hB,?_⟩
    apply Finset.disjoint_iff_inter_eq_empty.mp
    exact hd.symm.mono (member_subset_support hB) (member_subset_support hA)

/-- Every member of an extremal twenty-triple family has exactly ten disjoint members. -/
theorem extremal_twenty_disjoint_trace_card_ten
    {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hu : ∀ P ∈ L, P.card = 3) (hf : IsSunflowerFree L 3) (hc : L.card = 20)
    (A : Finset α) (hA : A ∈ L) : (exactTrace L A ∅).card = 10 := by
  classical
  obtain ⟨H,K,hLK,hdis,hparams⟩ := extremal_twenty_two_disjoint_designs L hu hf hc
  obtain ⟨hHc,hHi,_⟩ := hparams H (by simp)
  obtain ⟨hKc,hKi,_⟩ := hparams K (by simp)
  rw [hLK] at hA ⊢
  rcases Finset.mem_union.mp hA with hA | hA
  · rw [disjoint_trace_eq_other_component H K hHi hdis A hA]
    exact hKc
  · rw [Finset.union_comm,disjoint_trace_eq_other_component K H hKi hdis.symm A hA]
    exact hHc

/-- The singleton exact trace becomes the empty trace after deleting the anchor point. -/
theorem singleton_residual_eq_empty_link_trace
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α) (x : α)
    (hx : x ∈ R) :
    residualLink (exactTrace F R {x}) {x} =
      exactTrace (residualLink F {x}) (R \ {x}) ∅ := by
  classical
  ext P
  constructor
  · intro hP
    obtain ⟨S,hS,hxS,hSP⟩ := mem_residualLink_iff.mp hP
    have hSF := (Finset.mem_filter.mp hS).1
    refine Finset.mem_filter.mpr ⟨mem_residualLink_iff.mpr ⟨S,hSF,hxS,hSP⟩,?_⟩
    exact Finset.disjoint_iff_inter_eq_empty.mp
      ((Erdos20ThreeCrossEdges.residual_exact_trace_disjoint_anchor F R {x} P
        (mem_residualLink_iff.mpr ⟨S,hS,hxS,hSP⟩)).mono_right Finset.sdiff_subset)
  · intro hP
    obtain ⟨hPL,hPA⟩ := Finset.mem_filter.mp hP
    obtain ⟨S,hSF,hxS,hSP⟩ := mem_residualLink_iff.mp hPL
    refine mem_residualLink_iff.mpr ⟨S,Finset.mem_filter.mpr ⟨hSF,?_⟩,hxS,hSP⟩
    apply Finset.Subset.antisymm
    · intro y hy
      obtain ⟨hyS,hyR⟩ := Finset.mem_inter.mp hy
      by_contra hyx
      have hyP : y ∈ P := by rw [← hSP]; exact Finset.mem_sdiff.mpr ⟨hyS,hyx⟩
      have hyA : y ∈ R \ {x} := Finset.mem_sdiff.mpr ⟨hyR,hyx⟩
      have hm := Finset.mem_inter.mpr ⟨hyP,hyA⟩
      rw [hPA] at hm
      exact Finset.notMem_empty y hm
    · intro y hy
      have he := Finset.mem_singleton.mp hy
      subst y
      exact Finset.mem_inter.mpr ⟨hxS (by simp),hx⟩

/-- A degree-twenty point saturates its singleton trace at every incident anchor. -/
theorem degree_twenty_forces_singleton_trace_ten
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α) (x : α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hx : x ∈ R) (hd : (F.filter (fun S => x ∈ S)).card = 20) :
    (exactTrace F R {x}).card = 10 := by
  classical
  let L := residualLink F {x}
  have hLu : ∀ P ∈ L, P.card = 3 := by
    simpa [L] using residualLink_uniform (core := {x}) hu
  have hLf : IsSunflowerFree L 3 := residualLink_sunflowerFree hf
  have hLc : L.card = 20 := by simpa [L,card_residualLink,upperStar] using hd
  have hAL : R \ {x} ∈ L := mem_residualLink_iff.mpr ⟨R,hR,by simpa,rfl⟩
  have hcount := extremal_twenty_disjoint_trace_card_ten L hLu hLf hLc (R \ {x}) hAL
  rw [← singleton_residual_eq_empty_link_trace F R x hx,exact_trace_card_residual] at hcount
  exact hcount

/-- A point-degree cap bounds every meeting neighborhood by twice the cap plus nineteen. -/
theorem meeting_card_le_twice_degree_add_nineteen
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α) (D : ℕ)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hd : ∀ x ∈ R, (F.filter (fun S => x ∈ S)).card ≤ D) :
    (F.filter (fun S => (S ∩ R).Nonempty)).card ≤ 2*D+19 := by
  classical
  let N := F.filter (fun S => (S ∩ R).Nonempty)
  have hNF : N ⊆ F := Finset.filter_subset _ _
  have hRN : R ∈ N := Finset.mem_filter.mpr ⟨hR,by
    rw [Finset.inter_self]; exact Finset.card_pos.mp (by rw [hu R hR]; decide)⟩
  have hNu : ∀ S ∈ N, S.card = 4 := fun S hS => hu S (hNF hS)
  have hNf : IsSunflowerFree N 3 := fun H hH hsun => hf H (hH.trans hNF) hsun
  have hhit : ∀ S ∈ N, (S ∩ R).Nonempty := fun S hS => (Finset.mem_filter.mp hS).2
  have hinc := meeting_incidence_singleton_defect N R hRN (hu R hR) hhit
  have hsingle := singleton_intersection_card_le_forty N R hRN hNu hNf
  have hsum : (∑ x ∈ R, (N.filter (fun S => x ∈ S)).card) ≤ 4*D := by
    calc
      _ ≤ ∑ _x ∈ R, D := Finset.sum_le_sum (fun x hx =>
        (Finset.card_le_card (Finset.filter_subset_filter _ hNF)).trans (hd x hx))
      _ = 4*D := by simp [hu R hR]
  change N.card ≤ 2*D+19
  omega

/-- A uniform degree cap gives a closed degree-sensitive unrestricted upper bound. -/
theorem rank_four_card_le_max_degree_bound
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (D : ℕ)
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hd : ∀ x, (F.filter (fun S => x ∈ S)).card ≤ D) :
    F.card ≤ max 82 ((10*D+95)/3) := by
  classical
  by_contra hn
  have hlo : 82 < F.card ∧ (10*D+95)/3 < F.card := by omega
  have hne : F.Nonempty := Finset.card_pos.mp (by omega)
  letI : Nonempty F := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  have hmin : F.card - (2*D+19) ≤ (disjointnessGraph F).minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro R
    rw [rank_four_disjointnessGraph_degree_eq F hu R]
    have hN := meeting_card_le_twice_degree_add_nineteen F R.val D R.property hu hf
      (fun x _ => hd x)
    have hs := Finset.filter_card_add_filter_neg_card_eq_card
      (s := F) (p := fun S => (S ∩ R.val).Nonempty)
    simp only [Finset.not_nonempty_iff_eq_empty] at hs
    omega
  have hcol : (disjointnessGraph F).Colorable 2 := by
    apply SimpleGraph.colorable_of_cliqueFree_lt_minDegree
      (disjointnessGraph_triangle_free F hf)
    have hcard : Fintype.card F = F.card := Fintype.card_coe _
    simp only [hcard]
    omega
  have h82 := rank_four_card_le_eighty_two_of_two_colorable F hu hf hcol
  omega

/-- The target upper bound82 holds whenever all point degrees are at most fifteen. -/
theorem rank_four_card_le_eighty_two_of_degree_le_fifteen
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hd : ∀ x, (F.filter (fun S => x ∈ S)).card ≤ 15) : F.card ≤ 82 := by
  simpa using rank_four_card_le_max_degree_bound F 15 hu hf hd

/-- Any obstruction to the desired upper bound82 must contain a degree16–20 point. -/
theorem rank_four_large_forces_high_degree
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3) (hc : 83 ≤ F.card) :
    ∃ x : α, 16 ≤ (F.filter (fun S => x ∈ S)).card ∧
      (F.filter (fun S => x ∈ S)).card ≤ 20 := by
  classical
  have hn : ¬ ∀ x, (F.filter (fun S => x ∈ S)).card ≤ 15 := by
    intro hd
    have hle := rank_four_card_le_eighty_two_of_degree_le_fifteen F hu hf hd
    omega
  push_neg at hn
  obtain ⟨x,hx⟩ := hn
  exact ⟨x,by omega,rank_four_degree_le_twenty F hu hf x⟩

open Erdos20SaturatedMeeting

private theorem degree_meeting_arithmetic (D S P T n : ℕ)
    (hD : D≤19) (hS : S≤40) (hW : 3*S+2*P≤144)
    (hI : S+2*P+3*T+4≤4*D) (_hT : T≤4) (hN : n=1+S+P+T) : n≤D+36 := by omega

set_option maxHeartbeats 600000 in
/-- Below degree twenty, the weighted trace inequalities improve the cap by one. -/
theorem all_meeting_card_le_degree_add_thirty_six
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α) (D : ℕ)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hhit : ∀ S ∈ F, (S ∩ R).Nonempty) (hD : D ≤ 19)
    (hd : ∀ x ∈ R, (F.filter (fun S => x ∈ S)).card ≤ D) : F.card ≤ D+36 := by
  classical
  obtain ⟨x,y,z,w,hxy,hxz,hxw,hyz,hyw,hzw,hshape⟩ := Finset.card_eq_four.mp (hu R hR)
  subst R
  let n : Finset α → ℕ := fun C => (exactTrace F {x,y,z,w} C).card
  have hpart := card_eq_sum_exact_traces F {x,y,z,w}
  change F.card = ∑ C ∈ ({x,y,z,w} : Finset α).powerset, n C at hpart
  rw [sum_powerset_four n x y z w hxy hxz hxw hyz hyw hzw] at hpart
  have h0 : n ∅ = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro S hS
    obtain ⟨hSF,hSR⟩ := Finset.mem_filter.mp hS
    have hn := hhit S hSF
    rw [hSR] at hn
    exact Finset.not_nonempty_empty hn
  have h4 : n {x,y,z,w} = 1 := full_trace_card_eq_one F {x,y,z,w} 4 hR hu
  have heY : ({y,x,z,w} : Finset α) = {x,y,z,w} := by ext t; simp [or_left_comm]
  have heZ : ({z,x,y,w} : Finset α) = {x,y,z,w} := by ext t; simp [or_left_comm]
  have heW : ({w,x,y,z} : Finset α) = {x,y,z,w} := by ext t; simp [or_comm,or_left_comm]
  have hs1 := singleton_incident_pairs_weighted_le_thirty_six F x y z w
    hxy hxz hxw hyz hyw hzw hR hu hf
  have hs2 := singleton_incident_pairs_weighted_le_thirty_six F y x z w
    (Ne.symm hxy) hyz hyw hxz hxw hzw (by rw [heY]; exact hR) hu hf
  have hs3 := singleton_incident_pairs_weighted_le_thirty_six F z x y w
    (Ne.symm hxz) (Ne.symm hyz) hzw hxy hxw hyw (by rw [heZ]; exact hR) hu hf
  have hs4 := singleton_incident_pairs_weighted_le_thirty_six F w x y z
    (Ne.symm hxw) (Ne.symm hyw) (Ne.symm hzw) hxy hxz hyz (by rw [heW]; exact hR) hu hf
  rw [heY,Finset.pair_comm y x] at hs2
  rw [heZ,Finset.pair_comm z x,Finset.pair_comm z y] at hs3
  rw [heW,Finset.pair_comm w x,Finset.pair_comm w y,Finset.pair_comm w z] at hs4
  change 3 * n {x} + n {x,y} + n {x,z} + n {x,w} ≤ 36 at hs1
  change 3 * n {y} + n {x,y} + n {y,z} + n {y,w} ≤ 36 at hs2
  change 3 * n {z} + n {x,z} + n {y,z} + n {z,w} ≤ 36 at hs3
  change 3 * n {w} + n {x,w} + n {y,w} + n {z,w} ≤ 36 at hs4
  have ht (C : Finset α) (hC : C.card = 3) (hCR : C ⊆ ({x,y,z,w} : Finset α)) : n C ≤ 1 :=
    triple_trace_card_le_one F {x,y,z,w} C hR hu hf hCR hC
  have ht1 := ht {x,y,z} (by simp [hxy,hxz,hyz]) (by simp [Finset.insert_subset_iff])
  have ht2 := ht {x,y,w} (by simp [hxy,hxw,hyw]) (by simp [Finset.insert_subset_iff])
  have ht3 := ht {x,z,w} (by simp [hxz,hxw,hzw]) (by simp [Finset.insert_subset_iff])
  have ht4 := ht {y,z,w} (by simp [hyz,hyw,hzw]) (by simp)
  have hinc : (∑ C ∈ ({x,y,z,w} : Finset α).powerset, C.card * n C) ≤ 4*D := by
    rw [← incidence_eq_sum_weighted_exact_traces F {x,y,z,w}]
    calc
      _ ≤ ∑ _t ∈ ({x,y,z,w} : Finset α), D :=
        Finset.sum_le_sum (fun t ht => hd t ht)
      _ = 4*D := by simp [hxy,hxz,hxw,hyz,hyw,hzw]
  rw [sum_powerset_four (fun C => C.card * n C) x y z w hxy hxz hxw hyz hyw hzw] at hinc
  simp only [Finset.card_empty,zero_mul,Finset.card_singleton,one_mul] at hinc
  simp [hxy,hxz,hxw,hyz,hyw,hzw] at hinc
  let S := n {x}+n {y}+n {z}+n {w}
  let P := n {x,y}+n {x,z}+n {x,w}+n {y,z}+n {y,w}+n {z,w}
  let T := n {x,y,z}+n {x,y,w}+n {x,z,w}+n {y,z,w}
  have hSp : S ≤ 40 := by
    have hx := singleton_trace_card_le_ten F {x,y,z,w} {x} hR hu hf (by simp)
    have hy := singleton_trace_card_le_ten F {x,y,z,w} {y} hR hu hf (by simp)
    have hz := singleton_trace_card_le_ten F {x,y,z,w} {z} hR hu hf (by simp)
    have hw := singleton_trace_card_le_ten F {x,y,z,w} {w} hR hu hf (by simp)
    change n {x} ≤ 10 at hx
    change n {y} ≤ 10 at hy
    change n {z} ≤ 10 at hz
    change n {w} ≤ 10 at hw
    dsimp only [S]
    clear * - hx hy hz hw
    omega
  have hWp : 3*S+2*P≤144 := by
    dsimp only [S,P]
    clear * - hs1 hs2 hs3 hs4
    omega
  have hIp : S+2*P+3*T+4≤4*D := by
    dsimp only [S,P,T]
    clear * - hinc h4
    omega
  have hTp : T≤4 := by
    dsimp only [T]
    clear * - ht1 ht2 ht3 ht4
    omega
  have hNp : F.card=1+S+P+T := by
    dsimp only [S,P,T]
    clear * - hpart h0 h4
    omega
  exact degree_meeting_arithmetic D S P T F.card hD hSp hWp hIp hTp hNp

/-- Every degree cap D yields the sharper meeting bound D+36. -/
theorem meeting_card_le_degree_add_thirty_six
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α) (D : ℕ)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hd : ∀ x ∈ R, (F.filter (fun S => x ∈ S)).card ≤ D) :
    (F.filter (fun S => (S ∩ R).Nonempty)).card ≤ D+36 := by
  classical
  by_cases hD : D≤19
  · let N := F.filter (fun S => (S ∩ R).Nonempty)
    have hNF : N ⊆ F := Finset.filter_subset _ _
    have hRN : R ∈ N := Finset.mem_filter.mpr ⟨hR,by
      rw [Finset.inter_self]; exact Finset.card_pos.mp (by rw [hu R hR]; decide)⟩
    exact all_meeting_card_le_degree_add_thirty_six N R D hRN
      (fun S hS => hu S (hNF hS))
      (fun H hH hsun => hf H (hH.trans hNF) hsun)
      (fun S hS => (Finset.mem_filter.mp hS).2) hD
      (fun x hx => (Finset.card_le_card (Finset.filter_subset_filter _ hNF)).trans (hd x hx))
  · have hb := Erdos20MeetingFiftySix.meeting_neighborhood_card_le_fifty_six F R hR hu hf
    omega

/-- A general meeting cap is converted to an unrestricted bound by the graph theorem. -/
theorem rank_four_card_le_max_of_meeting_bound
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (M : ℕ)
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hM : ∀ R ∈ F, (F.filter (fun S => (S ∩ R).Nonempty)).card ≤ M) :
    F.card ≤ max 82 (5*M/3) := by
  classical
  by_contra hn
  have hlo : 82 < F.card ∧ 5*M/3 < F.card := by omega
  have hne : F.Nonempty := Finset.card_pos.mp (by omega)
  letI : Nonempty F := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  have hmin : F.card - M ≤ (disjointnessGraph F).minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro R
    rw [rank_four_disjointnessGraph_degree_eq F hu R]
    have hN := hM R.val R.property
    have hs := Finset.filter_card_add_filter_neg_card_eq_card
      (s := F) (p := fun S => (S ∩ R.val).Nonempty)
    simp only [Finset.not_nonempty_iff_eq_empty] at hs
    omega
  have hcol : (disjointnessGraph F).Colorable 2 := by
    apply SimpleGraph.colorable_of_cliqueFree_lt_minDegree
      (disjointnessGraph_triangle_free F hf)
    have hcard : Fintype.card F = F.card := Fintype.card_coe _
    simp only [hcard]
    omega
  have h82 := rank_four_card_le_eighty_two_of_two_colorable F hu hf hcol
  omega

/-- The best of three checked degree-sensitive meeting caps. -/
def degreeMeetingCap (D : ℕ) : ℕ := min 56 (min (2*D+19) (D+36))

/-- The resulting unrestricted upper envelope. -/
def degreeGlobalCap (D : ℕ) : ℕ := max 82 (5*degreeMeetingCap D/3)

/-- The complete proved envelope for any natural degree cap. -/
theorem rank_four_card_le_degree_envelope
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (D : ℕ)
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hd : ∀ x, (F.filter (fun S => x ∈ S)).card ≤ D) : F.card ≤ degreeGlobalCap D := by
  apply rank_four_card_le_max_of_meeting_bound F (degreeMeetingCap D) hu hf
  intro R hR
  exact le_min (Erdos20MeetingFiftySix.meeting_neighborhood_card_le_fifty_six F R hR hu hf)
    (le_min (meeting_card_le_twice_degree_add_nineteen F R D hR hu hf (fun x _ => hd x))
      (meeting_card_le_degree_add_thirty_six F R D hR hu hf (fun x _ => hd x)))

/-- Kernel-reduced degree caps15 through20, paired with their unrestricted bounds. -/
theorem degree_envelope_values :
    List.map degreeMeetingCap [15,16,17,18,19,20] = [49,51,53,54,55,56] ∧
    List.map degreeGlobalCap [15,16,17,18,19,20] = [82,85,88,90,91,93] := by decide

/-- Any family with at least92 members has a fully saturated twenty-triple point link. -/
theorem rank_four_ninety_two_forces_degree_twenty
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3) (hc : 92 ≤ F.card) :
    ∃ x : α, (F.filter (fun S => x ∈ S)).card = 20 := by
  classical
  have hn : ¬ ∀ x, (F.filter (fun S => x ∈ S)).card ≤ 19 := by
    intro hd
    have hle := rank_four_card_le_degree_envelope F 19 hu hf hd
    change F.card ≤ 91 at hle
    omega
  push_neg at hn
  obtain ⟨x,hx⟩ := hn
  have hcap := rank_four_degree_le_twenty F hu hf x
  exact ⟨x,by omega⟩

end Erdos20V8Global
