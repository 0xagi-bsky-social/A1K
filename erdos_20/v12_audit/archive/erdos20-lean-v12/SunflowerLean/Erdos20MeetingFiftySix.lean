import SunflowerLean.Erdos20SaturatedMeeting
import SunflowerLean.Erdos20RankFourRefined
import SunflowerLean.Erdos20DesignNormalForm

/-! Equality analysis for the rank-four meeting-neighborhood bound. -/
namespace Erdos20MeetingFiftySix
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence
open Erdos20RankThree Erdos20RankFour Erdos20SaturatedMeeting
open Erdos20DesignSeparation

private theorem aggregate_saturation (S P T : ℕ)
    (hST : S+P+T=56) (hW : 3*S+2*P≤144) (hI : S+2*P+3*T≤76) (hT : T≤4) :
    S=40 ∧ P=12 ∧ T=4 := by omega

private theorem four_equal_of_bounded_sum (a b c d k : ℕ)
    (ha : a ≤ k) (hb : b ≤ k) (hc : c ≤ k) (hd : d ≤ k)
    (hs : a+b+c+d=4*k) : a=k ∧ b=k ∧ c=k ∧ d=k := by omega

set_option maxHeartbeats 600000 in
/-- Equality at fifty-seven saturates every singleton trace, triple trace, and anchor degree. -/
theorem fifty_seven_saturated_profile
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hhit : ∀ S ∈ F, (S ∩ R).Nonempty) (hc : F.card = 57) :
    (∀ x ∈ R, (exactTrace F R {x}).card = 10 ∧
      (F.filter (fun S => x ∈ S)).card = 20) ∧
    ∀ x ∈ R, (exactTrace F R (R.erase x)).card = 1 := by
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
  have hinc : (∑ C ∈ ({x,y,z,w} : Finset α).powerset, C.card * n C) ≤ 80 := by
    rw [← incidence_eq_sum_weighted_exact_traces F {x,y,z,w}]
    calc
      _ ≤ ∑ _t ∈ ({x,y,z,w} : Finset α), 20 :=
        Finset.sum_le_sum (fun t _ => rank_four_degree_le_twenty F hu hf t)
      _ = 80 := by simp [hxy,hxz,hxw,hyz,hyw,hzw]
  rw [sum_powerset_four (fun C => C.card * n C) x y z w hxy hxz hxw hyz hyw hzw] at hinc
  simp only [Finset.card_empty,zero_mul,Finset.card_singleton,one_mul] at hinc
  simp [hxy,hxz,hxw,hyz,hyw,hzw] at hinc
  have hn1 := singleton_trace_card_le_ten F {x,y,z,w} {x} hR hu hf (by simp)
  have hn2 := singleton_trace_card_le_ten F {x,y,z,w} {y} hR hu hf (by simp)
  have hn3 := singleton_trace_card_le_ten F {x,y,z,w} {z} hR hu hf (by simp)
  have hn4 := singleton_trace_card_le_ten F {x,y,z,w} {w} hR hu hf (by simp)
  change n {x} ≤ 10 at hn1
  change n {y} ≤ 10 at hn2
  change n {z} ≤ 10 at hn3
  change n {w} ≤ 10 at hn4
  let S := n {x} + n {y} + n {z} + n {w}
  let P := n {x,y} + n {x,z} + n {x,w} + n {y,z} + n {y,w} + n {z,w}
  let T := n {x,y,z} + n {x,y,w} + n {x,z,w} + n {y,z,w}
  have hST : S + P + T = 56 := by
    dsimp only [S,P,T]
    clear hs1 hs2 hs3 hs4 hinc ht1 ht2 ht3 ht4 hn1 hn2 hn3 hn4
    omega
  have hW : 3*S + 2*P ≤ 144 := by
    dsimp only [S,P]
    clear hST hpart hinc ht1 ht2 ht3 ht4 hn1 hn2 hn3 hn4 hc
    omega
  have hI : S + 2*P + 3*T ≤ 76 := by
    dsimp only [S,P,T]
    clear hST hW hpart hs1 hs2 hs3 hs4 ht1 ht2 ht3 ht4 hn1 hn2 hn3 hn4 hc
    omega
  have hT : T ≤ 4 := by
    dsimp only [T]
    clear hST hW hI hpart hs1 hs2 hs3 hs4 hinc hn1 hn2 hn3 hn4 hc
    omega
  obtain ⟨hS,hP,hT4⟩ := aggregate_saturation S P T hST hW hI hT
  obtain ⟨hnx,hny,hnz,hnw⟩ := four_equal_of_bounded_sum (n {x}) (n {y}) (n {z}) (n {w}) 10
    hn1 hn2 hn3 hn4 hS
  obtain ⟨hnt1,hnt2,hnt3,hnt4⟩ := four_equal_of_bounded_sum
    (n {x,y,z}) (n {x,y,w}) (n {x,z,w}) (n {y,z,w}) 1 ht1 ht2 ht3 ht4 hT4
  have hIe := incidence_eq_sum_weighted_exact_traces F {x,y,z,w}
  change (∑ t ∈ ({x,y,z,w} : Finset α), (F.filter (fun S => t ∈ S)).card) =
    ∑ C ∈ ({x,y,z,w} : Finset α).powerset, C.card * n C at hIe
  rw [sum_powerset_four (fun C => C.card * n C) x y z w hxy hxz hxw hyz hyw hzw] at hIe
  simp [hxy,hxz,hxw,hyz,hyw,hzw] at hIe
  have hd1 := rank_four_degree_le_twenty F hu hf x
  have hd2 := rank_four_degree_le_twenty F hu hf y
  have hd3 := rank_four_degree_le_twenty F hu hf z
  have hd4 := rank_four_degree_le_twenty F hu hf w
  have htotal : (F.filter (fun S => x ∈ S)).card + (F.filter (fun S => y ∈ S)).card +
      (F.filter (fun S => z ∈ S)).card + (F.filter (fun S => w ∈ S)).card = 80 := by
    rw [hnx,hny,hnz,hnw,hnt1,hnt2,hnt3,hnt4,h4] at hIe
    dsimp only [P] at hP
    clear hpart hST hW hI hs1 hs2 hs3 hs4 hinc hn1 hn2 hn3 hn4 ht1 ht2 ht3 ht4
    omega
  obtain ⟨hdx,hdy,hdz,hdw⟩ := four_equal_of_bounded_sum
    (F.filter (fun S => x ∈ S)).card (F.filter (fun S => y ∈ S)).card
    (F.filter (fun S => z ∈ S)).card (F.filter (fun S => w ∈ S)).card 20
    hd1 hd2 hd3 hd4 htotal
  constructor
  · intro t htR
    simp only [Finset.mem_insert,Finset.mem_singleton] at htR
    rcases htR with rfl | rfl | rfl | rfl
    · exact ⟨hnx,hdx⟩
    · exact ⟨hny,hdy⟩
    · exact ⟨hnz,hdz⟩
    · exact ⟨hnw,hdw⟩
  · intro t htR
    simp only [Finset.mem_insert,Finset.mem_singleton] at htR
    rcases htR with ht | ht | ht | ht
    · subst t
      simpa [n,Finset.erase_insert_of_ne,Finset.erase_insert,hxy,hxz,hxw] using hnt4
    · subst t
      simpa [n,Finset.erase_insert_of_ne,Finset.erase_insert,hxy,Ne.symm hxy,hyz,hyw] using hnt3
    · subst t
      simpa [n,Finset.erase_insert_of_ne,Finset.erase_insert,hxz,hyz,Ne.symm hxz,Ne.symm hyz,hzw] using hnt2
    · subst t
      simpa [n,Finset.erase_insert_of_ne,Finset.erase_insert,hxw,hyw,hzw,Ne.symm hxw,Ne.symm hyw,Ne.symm hzw] using hnt1

/-- The part of a point link that is not its singleton exact-trace residue. -/
def complementaryPointLink {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (R : Finset α) (x : α) : Finset (Finset α) :=
  residualLink F {x} \ residualLink (exactTrace F R {x}) {x}

/-- Saturation gives a second ten-member design inside the point link. -/
theorem complementary_point_link_design
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α) (x : α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hs : (exactTrace F R {x}).card = 10)
    (hd : (F.filter (fun S => x ∈ S)).card = 20) :
    let K := complementaryPointLink F R x
    (∀ S ∈ K, S.card = 3) ∧ IsSunflowerFree K 3 ∧ K.card = 10 ∧
    (∀ S ∈ K, ∀ T ∈ K, (S ∩ T).Nonempty) ∧ (support K).card = 6 ∧
    (∀ y ∈ support K, ∀ z ∈ support K, y ≠ z →
      (K.filter (fun S => ({y,z} : Finset α) ⊆ S)).card = 2) := by
  classical
  let L := residualLink F {x}
  let H := residualLink (exactTrace F R {x}) {x}
  have hLu : ∀ S ∈ L, S.card = 3 := by
    simpa [L] using residualLink_uniform (core := {x}) hu
  have hLf : IsSunflowerFree L 3 := residualLink_sunflowerFree hf
  have hHL : H ⊆ L := by
    intro P hP
    obtain ⟨S,hS,hxS,hSP⟩ := mem_residualLink_iff.mp hP
    exact mem_residualLink_iff.mpr ⟨S,(Finset.mem_filter.mp hS).1,hxS,hSP⟩
  have hHi : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty :=
    exact_trace_residual_intersecting F R {x} 4 hR hu hf (by simp)
  have hHc : H.card = 10 := by simpa [H,exact_trace_card_residual] using hs
  have hLc : L.card = 20 := by simpa [L,card_residualLink,upperStar] using hd
  obtain ⟨hKc,hKi,_,hKs,_,hKp⟩ := extremal_twenty_complement_design L H hLu hLf hHL hHi hHc hLc
  exact ⟨(fun S hS => hLu S (Finset.mem_sdiff.mp hS).1),
    (fun G hG hg => hLf G (hG.trans Finset.sdiff_subset) hg),hKc,hKi,hKs,hKp⟩

/-- A point residue meeting another anchor point belongs to the complementary link. -/
theorem member_residue_mem_complementary_link
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α)
    (x y : α) (S : Finset α) (hS : S ∈ F) (hxS : x ∈ S)
    (hyS : y ∈ S) (hyR : y ∈ R) (hyx : y ≠ x) :
    S \ {x} ∈ complementaryPointLink F R x := by
  classical
  refine Finset.mem_sdiff.mpr ⟨mem_residualLink_iff.mpr ⟨S,hS,by simpa,rfl⟩,?_⟩
  intro hh
  exact Finset.disjoint_left.mp
    (Erdos20ThreeCrossEdges.residual_exact_trace_disjoint_anchor F R {x} (S \ {x}) hh)
    (Finset.mem_sdiff.mpr ⟨hyS,by simpa⟩) hyR

/-- Every nonempty triple trace has a single outside extension point. -/
theorem triple_trace_has_outside_extension
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α) (m : α)
    (hu : ∀ S ∈ F, S.card = 4) (hR4 : R.card = 4) (hm : m ∈ R)
    (hc : (exactTrace F R (R.erase m)).card = 1) :
    ∃ q : α, q ∉ R ∧ insert q (R.erase m) ∈ F := by
  classical
  obtain ⟨S,hS⟩ := Finset.card_pos.mp (show 0 < (exactTrace F R (R.erase m)).card by omega)
  obtain ⟨hSF,hSR⟩ := Finset.mem_filter.mp hS
  have hCS : R.erase m ⊆ S := by rw [← hSR]; exact Finset.inter_subset_left
  have hr : (S \ R.erase m).card = 1 := by
    rw [Finset.card_sdiff_of_subset hCS,hu S hSF,Finset.card_erase_of_mem hm,hR4]
  obtain ⟨q,hq⟩ := Finset.card_eq_one.mp hr
  have hqm : q ∈ S \ R.erase m := by rw [hq]; simp
  have hqR : q ∉ R := by
    intro h
    apply (Finset.mem_sdiff.mp hqm).2
    rw [← hSR]
    exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hqm).1,h⟩
  refine ⟨q,hqR,?_⟩
  have he : insert q (R.erase m) = S := by
    rw [← Finset.singleton_union,Finset.union_comm,← hq]
    exact Finset.union_sdiff_of_subset hCS
  rw [he]
  exact hSF

/-- Four points contain a point outside any specified pair. -/
theorem four_set_has_third_point
    {α : Type*} [DecidableEq α] (R : Finset α) (hR : R.card = 4) (m n : α) :
    ∃ x ∈ R, x ≠ m ∧ x ≠ n := by
  classical
  by_contra hn
  push_neg at hn
  have hs : R ⊆ {m,n} := by
    intro x hx
    by_cases he : x = m
    · simp [he]
    · simp [hn x hx he]
  have hle := Finset.card_le_card hs
  have hc : ({m,n} : Finset α).card ≤ 2 := Finset.card_le_two
  omega

/-- The anchor with one point deleted belongs to its complementary point link. -/
theorem anchor_mem_complementary_link
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α) (x : α)
    (hR : R ∈ F) (hR4 : R.card = 4) (hx : x ∈ R) :
    R.erase x ∈ complementaryPointLink F R x := by
  obtain ⟨y,hy,hyx,_⟩ := four_set_has_third_point R hR4 x x
  simpa [Finset.sdiff_singleton_eq_erase] using
    member_residue_mem_complementary_link F R x y R hR hx hy hy hyx

/-- A triple-trace extension induces a pair extension in any other complementary link. -/
theorem extension_mem_complementary_link
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α) (x m q : α)
    (hR4 : R.card = 4) (hx : x ∈ R) (hxm : x ≠ m) (hq : q ∉ R)
    (he : insert q (R.erase m) ∈ F) :
    insert q ((R.erase x).erase m) ∈ complementaryPointLink F R x := by
  classical
  obtain ⟨y,hy,hyx,hym⟩ := four_set_has_third_point R hR4 x m
  have hxS : x ∈ insert q (R.erase m) := by simp [hxm,hx]
  have hyS : y ∈ insert q (R.erase m) := by simp [hym,hy]
  have hl := member_residue_mem_complementary_link F R x y (insert q (R.erase m)) he hxS hyS hy hyx
  convert hl using 1
  ext t
  simp only [Finset.mem_insert,Finset.mem_erase,Finset.mem_sdiff,Finset.mem_singleton]
  have hqx : q ≠ x := fun h => hq (h ▸ hx)
  aesop

set_option maxHeartbeats 800000 in
/-- Four saturated point links and all four triple traces cannot coexist. -/
theorem no_saturated_anchor_profile
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hs : ∀ x ∈ R, (exactTrace F R {x}).card = 10 ∧
      (F.filter (fun S => x ∈ S)).card = 20)
    (ht : ∀ x ∈ R, (exactTrace F R (R.erase x)).card = 1) : False := by
  classical
  have hR4 := hu R hR
  have hExt : ∀ m ∈ R, ∃ q : α, q ∉ R ∧ insert q (R.erase m) ∈ F :=
    fun m hm => triple_trace_has_outside_extension F R m hu hR4 hm (ht m hm)
  choose z hz using hExt
  let z' : α → α := fun m => if hm : m ∈ R then z m hm else m
  have hz' (m : α) (hm : m ∈ R) : z' m ∉ R ∧ insert (z' m) (R.erase m) ∈ F := by
    simpa [z',hm] using hz m hm
  let K : α → Finset (Finset α) := complementaryPointLink F R
  have hDesign (x : α) (hx : x ∈ R) :=
    complementary_point_link_design F R x hR hu hf (hs x hx).1 (hs x hx).2
  have hAnchor (x : α) (hx : x ∈ R) : R.erase x ∈ K x :=
    anchor_mem_complementary_link F R x hR hR4 hx
  have hInduced (x m : α) (hx : x ∈ R) (hm : m ∈ R) (hxm : x ≠ m) :
      insert (z' m) ((R.erase x).erase m) ∈ K x :=
    extension_mem_complementary_link F R x m (z' m) hR4 hx hxm (hz' m hm).1 (hz' m hm).2
  have hInj : Set.InjOn z' (↑R : Set α) := by
    intro m hm n hn he
    by_contra hmn
    obtain ⟨x,hx,hxm,hxn⟩ := four_set_has_third_point R hR4 m n
    obtain ⟨hKu,hKf,hKc,hKi,_,_⟩ := hDesign x hx
    apply Erdos20DesignNormalForm.ten_forbids_common_outside_extension (K x) hKu hKf hKi hKc
      (R.erase x) (hAnchor x hx) m n
      (Finset.mem_erase.mpr ⟨Ne.symm hxm,hm⟩) (Finset.mem_erase.mpr ⟨Ne.symm hxn,hn⟩)
      hmn (z' m) (fun hh => (hz' m hm).1 (Finset.mem_of_mem_erase hh))
      (hInduced x m hx hm hxm)
    rw [he]
    exact hInduced x n hx hn hxn
  have hSupport (x : α) (hx : x ∈ R) :
      support (K x) = R.erase x ∪ (R.erase x).image z' := by
    obtain ⟨_,_,_,_,hcard,_⟩ := hDesign x hx
    have hsA : R.erase x ⊆ support (K x) := member_subset_support (hAnchor x hx)
    have hsZ : (R.erase x).image z' ⊆ support (K x) := by
      intro q hq
      obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hq
      exact member_subset_support (hInduced x m hx (Finset.mem_of_mem_erase hm)
        (Ne.symm (Finset.mem_erase.mp hm).1)) (by simp)
    have hdis : Disjoint (R.erase x) ((R.erase x).image z') := by
      apply Finset.disjoint_left.mpr
      intro q hqA hqZ
      obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hqZ
      exact (hz' m (Finset.mem_of_mem_erase hm)).1 (Finset.mem_of_mem_erase hqA)
    have hAc : (R.erase x).card = 3 := by rw [Finset.card_erase_of_mem hx,hR4]
    have hZc : ((R.erase x).image z').card = 3 := by
      rw [Finset.card_image_of_injOn (fun m hm n hn => hInj (Finset.mem_of_mem_erase hm)
        (Finset.mem_of_mem_erase hn)),hAc]
    symm
    exact Finset.eq_of_subset_of_card_le (Finset.union_subset hsA hsZ)
      (by rw [Finset.card_union_of_disjoint hdis,hAc,hZc,hcard])
  have hExcluded (x : α) (hx : x ∈ R) : z' x ∉ support (K x) := by
    rw [hSupport x hx]
    intro hm
    rcases Finset.mem_union.mp hm with hm | hm
    · exact (hz' x hx).1 (Finset.mem_of_mem_erase hm)
    · obtain ⟨m,hm,he⟩ := Finset.mem_image.mp hm
      have heq : m = x := hInj (Finset.mem_of_mem_erase hm) hx he
      exact (Finset.mem_erase.mp hm).1 heq
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < R.card by omega)
  obtain ⟨y,hy,hyx,_⟩ := four_set_has_third_point R hR4 x x
  have hxA : x ∈ R.erase y := Finset.mem_erase.mpr ⟨Ne.symm hyx,hx⟩
  have hxKy : x ∈ support (K y) := member_subset_support (hAnchor y hy) hxA
  have hzKy : z' x ∈ support (K y) := by
    rw [hSupport y hy]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hxA,rfl⟩)
  have hneq : x ≠ z' x := fun he => (hz' x hx).1 (he ▸ hx)
  obtain ⟨_,_,_,_,_,hp⟩ := hDesign y hy
  have hpair := hp x hxKy (z' x) hzKy hneq
  change ((K y).filter (fun S => ({x,z' x} : Finset α) ⊆ S)).card = 2 at hpair
  obtain ⟨P,hP⟩ := Finset.card_pos.mp
    (show 0 < ((K y).filter (fun S => ({x,z' x} : Finset α) ⊆ S)).card by omega)
  obtain ⟨hPK,hPair⟩ := Finset.mem_filter.mp hP
  have hPL : P ∈ residualLink F {y} := (Finset.mem_sdiff.mp hPK).1
  have hSF : ({y} : Finset α) ∪ P ∈ F := core_union_residual_mem_family hPL
  have hxP : x ∈ P := hPair (by simp)
  have hzP : z' x ∈ P := hPair (by simp)
  have hRes := member_residue_mem_complementary_link F R x y ({y} ∪ P) hSF
    (by simp [hxP]) (by simp) hy hyx
  apply hExcluded x hx
  apply member_subset_support hRes
  exact Finset.mem_sdiff.mpr ⟨by simp [hzP],by simpa using Ne.symm hneq⟩

/-- A rank-four family meeting one of its members contains at most fifty-six sets. -/
theorem all_meeting_anchor_card_le_fifty_six
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3)
    (hhit : ∀ S ∈ F, (S ∩ R).Nonempty) : F.card ≤ 56 := by
  have hle := all_meeting_anchor_card_le_fifty_seven F R hR hu hf hhit
  by_contra hh
  have hc : F.card = 57 := by omega
  obtain ⟨hs,ht⟩ := fifty_seven_saturated_profile F R hR hu hf hhit hc
  exact no_saturated_anchor_profile F R hR hu hf hs ht

/-- Every rank-four meeting neighborhood contains at most fifty-six members. -/
theorem meeting_neighborhood_card_le_fifty_six
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α)
    (hR : R ∈ F) (hu : ∀ S ∈ F, S.card = 4) (hf : IsSunflowerFree F 3) :
    (F.filter (fun S => (S ∩ R).Nonempty)).card ≤ 56 := by
  classical
  let N := F.filter (fun S => (S ∩ R).Nonempty)
  have hRN : R ∈ N := Finset.mem_filter.mpr ⟨hR,by
    rw [Finset.inter_self]; exact Finset.card_pos.mp (by rw [hu R hR]; decide)⟩
  exact all_meeting_anchor_card_le_fifty_six N R hRN
    (fun S hS => hu S (Finset.mem_filter.mp hS).1)
    (fun H hH hsun => hf H (hH.trans (Finset.filter_subset _ _)) hsun)
    (fun S hS => (Finset.mem_filter.mp hS).2)

end Erdos20MeetingFiftySix
