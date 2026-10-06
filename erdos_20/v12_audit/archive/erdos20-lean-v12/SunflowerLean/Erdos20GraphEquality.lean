import SunflowerLean.Erdos20RankThree

/-! Equality structure for sunflower-free graphs. -/
namespace Erdos20GraphEquality

open Erdos20CrossBounds Erdos20RankThree Erdos20Incidence

/-- A three-edge intersecting graph of maximum degree two is a triangle. -/
theorem intersecting_three_edges_triangle
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 2)
    (hd : ∀ x, (F.filter (fun S => x ∈ S)).card ≤ 2)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty)
    (hc : F.card = 3) :
    ∃ x y z : α, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      F = {{x,y}, {x,z}, {y,z}} := by
  classical
  obtain ⟨B,C,D,hBC,hBD,hCD,hF⟩ := Finset.card_eq_three.mp hc
  have hBF : B ∈ F := by simp [hF]
  have hCF : C ∈ F := by simp [hF]
  have hDF : D ∈ F := by simp [hF]
  obtain ⟨x,hx⟩ := hi B hBF C hCF
  obtain ⟨hxB,hxC⟩ := Finset.mem_inter.mp hx
  have heB : (B.erase x).card = 1 := by rw [Finset.card_erase_of_mem hxB, hu B hBF]
  have heC : (C.erase x).card = 1 := by rw [Finset.card_erase_of_mem hxC, hu C hCF]
  obtain ⟨y,hy⟩ := Finset.card_eq_one.mp heB
  obtain ⟨z,hz⟩ := Finset.card_eq_one.mp heC
  have hB : B = {x,y} := by rw [← Finset.insert_erase hxB, hy]
  have hC : C = {x,z} := by rw [← Finset.insert_erase hxC, hz]
  have hxy : x ≠ y := by
    intro he; have := hu B hBF; simp [hB, he] at this
  have hxz : x ≠ z := by
    intro he; have := hu C hCF; simp [hC, he] at this
  have hyz : y ≠ z := by intro he; apply hBC; rw [hB,hC,he]
  have hxD : x ∉ D := by
    intro h
    have he : F.filter (fun S => x ∈ S) = F := by
      apply Finset.filter_eq_self.mpr
      intro S hS
      simp only [hF,Finset.mem_insert,Finset.mem_singleton] at hS
      rcases hS with rfl | rfl | rfl <;> assumption
    have := hd x
    rw [he,hc] at this
    omega
  have hyD : y ∈ D := by
    obtain ⟨w,hw⟩ := hi D hDF B hBF
    have hwD := (Finset.mem_inter.mp hw).1
    have hwB := (Finset.mem_inter.mp hw).2
    simp only [hB,Finset.mem_insert,Finset.mem_singleton] at hwB
    rcases hwB with rfl | rfl
    · exact False.elim (hxD hwD)
    · exact hwD
  have hzD : z ∈ D := by
    obtain ⟨w,hw⟩ := hi D hDF C hCF
    have hwD := (Finset.mem_inter.mp hw).1
    have hwC := (Finset.mem_inter.mp hw).2
    simp only [hC,Finset.mem_insert,Finset.mem_singleton] at hwC
    rcases hwC with rfl | rfl
    · exact False.elim (hxD hwD)
    · exact hwD
  have hD : D = {y,z} := by
    apply Eq.symm
    apply Finset.eq_of_subset_of_card_le
    · simp [Finset.insert_subset_iff,hyD,hzD]
    · simp [hu D hDF,hyz]
  exact ⟨x,y,z,hxy,hxz,hyz,by rw [hF,hB,hC,hD]⟩

/-- A point whose degree is already saturated in a subfamily has no further edges. -/
theorem saturated_point_no_extra_edge
    {α : Type*} [DecidableEq α] (F G : Finset (Finset α)) (x : α) (d : ℕ)
    (hsub : G ⊆ F)
    (hF : (F.filter (fun S => x ∈ S)).card ≤ d)
    (hG : (G.filter (fun S => x ∈ S)).card = d)
    (S : Finset α) (hS : S ∈ F) (hx : x ∈ S) : S ∈ G := by
  have hs : G.filter (fun S => x ∈ S) ⊆ F.filter (fun S => x ∈ S) :=
    Finset.filter_subset_filter _ hsub
  have he : G.filter (fun S => x ∈ S) = F.filter (fun S => x ∈ S) :=
    Finset.eq_of_subset_of_card_le hs (by omega)
  have hm : S ∈ G.filter (fun S => x ∈ S) := by
    rw [he]
    exact Finset.mem_filter.mpr ⟨hS,hx⟩
  exact (Finset.mem_filter.mp hm).1

/-- A triangle in a graph of maximum degree two is an isolated component. -/
theorem triangle_isolated
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x y z : α)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hd : ∀ a, (F.filter (fun S => a ∈ S)).card ≤ 2)
    (hsub : ({{x,y},{x,z},{y,z}} : Finset (Finset α)) ⊆ F)
    (S : Finset α) (hS : S ∈ F)
    (hnot : S ∉ ({{x,y},{x,z},{y,z}} : Finset (Finset α))) :
    S ∩ {x,y,z} = ∅ := by
  let G : Finset (Finset α) := {{x,y},{x,z},{y,z}}
  have hexyxz : ({x,y} : Finset α) ≠ {x,z} := by
    intro he
    have hyin : y ∈ ({x,z} : Finset α) := by rw [← he]; simp
    simpa [Ne.symm hxy,hyz] using hyin
  have hexyyz : ({x,y} : Finset α) ≠ {y,z} := by
    intro he
    have hxin : x ∈ ({y,z} : Finset α) := by rw [← he]; simp
    simpa [hxy,hxz] using hxin
  have hexzyz : ({x,z} : Finset α) ≠ {y,z} := by
    intro he
    have hxin : x ∈ ({y,z} : Finset α) := by rw [← he]; simp
    simpa [hxy,hxz] using hxin
  have hGx : (G.filter (fun T => x ∈ T)).card = 2 := by
    simp [G, Finset.filter_insert, Finset.filter_singleton, hxy, hxz, hexyxz]
  have hGy : (G.filter (fun T => y ∈ T)).card = 2 := by
    simp [G, Finset.filter_insert, Finset.filter_singleton, Ne.symm hxy, hyz, hexyyz]
  have hGz : (G.filter (fun T => z ∈ T)).card = 2 := by
    simp [G, Finset.filter_insert, Finset.filter_singleton, Ne.symm hxz, Ne.symm hyz, hexzyz]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨haS,haV⟩ := Finset.mem_inter.mp ha
  simp only [Finset.mem_insert,Finset.mem_singleton] at haV
  rcases haV with he | he | he
  · subst a; exact hnot (saturated_point_no_extra_edge F G x 2 hsub (hd x) hGx S hS haS)
  · subst a; exact hnot (saturated_point_no_extra_edge F G y 2 hsub (hd y) hGy S hS haS)
  · subst a; exact hnot (saturated_point_no_extra_edge F G z 2 hsub (hd z) hGz S hS haS)

/-- At most three edges meet a fixed member in a maximum-degree-two graph. -/
theorem graph_meeting_neighborhood_card_le_three
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (R : Finset α)
    (hR : R ∈ F) (hRcard : R.card = 2)
    (hd : ∀ x, (F.filter (fun S => x ∈ S)).card ≤ 2) :
    (F.filter (fun S => (S ∩ R).Nonempty)).card ≤ 3 := by
  classical
  let N := F.filter (fun S => (S ∩ R).Nonempty)
  have hRN : R ∈ N := by
    apply Finset.mem_filter.mpr
    exact ⟨hR,by simpa using Finset.card_pos.mp (by omega : 0 < R.card)⟩
  have hlo := incidence_defect_lower_bound N {R} R 2
    (by simpa using hRN) (by simpa using hRcard) (by simp)
    (fun S hS => (Finset.mem_filter.mp hS).2)
  have hdN : ∀ x, (N.filter (fun S => x ∈ S)).card ≤ 2 := by
    intro x
    exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans (hd x)
  have hhi : (∑ x ∈ R, (N.filter (fun S => x ∈ S)).card) ≤ 4 := by
    calc
      _ ≤ ∑ _x ∈ R, 2 := Finset.sum_le_sum (fun x _ => hdN x)
      _ = 4 := by simp [hRcard]
  simpa using Nat.le_of_add_le_add_right (show N.card + 1 ≤ 3 + 1 by simpa using hlo.trans hhi)

/-- Equality in the six-edge bound is rigid: precisely two disjoint triangles. -/
theorem six_edges_two_disjoint_triangles
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 2) (hf : IsSunflowerFree F 3) (hc : F.card = 6) :
    ∃ x y z u v w : α,
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      Disjoint ({x,y,z} : Finset α) {u,v,w} ∧
      F = {{x,y},{x,z},{y,z}} ∪ {{u,v},{u,w},{v,w}} := by
  classical
  have hd := rank_two_three_petals_degree_le_two F hu hf
  obtain ⟨R,hR⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
  let D := F.filter (fun S => S ∩ R = ∅)
  have hsubD : D ⊆ F := Finset.filter_subset _ _
  have huD : ∀ S ∈ D, S.card = 2 := fun S hS => hu S (hsubD hS)
  have hfD : IsSunflowerFree D 3 := fun H hH hsun => hf H (hH.trans hsubD) hsun
  have hiD : ∀ S ∈ D, ∀ T ∈ D, (S ∩ T).Nonempty := by
    intro S hS T hT
    exact disjoint_anchor_family_intersecting F R hR
      (Finset.card_pos.mp (by rw [hu R hR]; decide)) hf S hS T hT
      (Finset.card_pos.mp (by rw [huD S hS]; decide))
      (Finset.card_pos.mp (by rw [huD T hT]; decide))
  have hDle := intersecting_rank_two_three_petals_card_le_three D huD hfD hiD
  have hNle := graph_meeting_neighborhood_card_le_three F R hR (hu R hR) hd
  have hsplit : F.card = (F.filter (fun S => (S ∩ R).Nonempty)).card + D.card := by
    have hs := Finset.filter_card_add_filter_neg_card_eq_card (s := F) (p := fun S => (S ∩ R).Nonempty)
    simpa [D, Finset.not_nonempty_iff_eq_empty] using hs.symm
  have hcD : D.card = 3 := by omega
  obtain ⟨x,y,z,hxy,hxz,hyz,hD⟩ := intersecting_three_edges_triangle D huD
    (rank_two_three_petals_degree_le_two D huD hfD) hiD hcD
  let H := F \ D
  have hsubH : H ⊆ F := Finset.sdiff_subset
  have huH : ∀ S ∈ H, S.card = 2 := fun S hS => hu S (hsubH hS)
  have hfH : IsSunflowerFree H 3 := fun J hJ hsun => hf J (hJ.trans hsubH) hsun
  have hcross : ∀ S ∈ H, S ∩ {x,y,z} = ∅ := by
    intro S hS
    obtain ⟨hSF,hSD⟩ := Finset.mem_sdiff.mp hS
    exact triangle_isolated F x y z hxy hxz hyz hd
      (by rw [← hD]; exact hsubD) S hSF (by rwa [← hD])
  have hxyF : ({x,y} : Finset α) ∈ F := hsubD (by simp [hD])
  have hHdis : H ⊆ F.filter (fun S => S ∩ {x,y} = ∅) := by
    intro S hS
    refine Finset.mem_filter.mpr ⟨hsubH hS, ?_⟩
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hx : a ∈ S ∩ {x,y,z} := by
      obtain ⟨haS,haV⟩ := Finset.mem_inter.mp ha
      exact Finset.mem_inter.mpr ⟨haS,by simpa only [Finset.mem_insert,Finset.mem_singleton] using Or.imp_right Or.inl (show a = x ∨ a = y by simpa using haV)⟩
    simpa [hcross S hS] using hx
  have hiH : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty := by
    intro S hS T hT
    exact disjoint_anchor_family_intersecting F {x,y} hxyF (by simp) hf
      S (hHdis hS) T (hHdis hT)
      (Finset.card_pos.mp (by rw [huH S hS]; decide))
      (Finset.card_pos.mp (by rw [huH T hT]; decide))
  have hcH : H.card = 3 := by
    dsimp [H]
    rw [Finset.card_sdiff_of_subset hsubD,hc,hcD]
  obtain ⟨u,v,w,huv,huw,hvw,hH⟩ := intersecting_three_edges_triangle H huH
    (rank_two_three_petals_degree_le_two H huH hfH) hiH hcH
  have huout : u ∉ ({x,y,z} : Finset α) := by
    intro hum
    have he := hcross {u,v} (by simp [hH])
    have hm : u ∈ ({u,v} : Finset α) ∩ {x,y,z} := by simp [hum]
    simpa [he] using hm
  have hvout : v ∉ ({x,y,z} : Finset α) := by
    intro hvm
    have he := hcross {u,v} (by simp [hH])
    have hm : v ∈ ({u,v} : Finset α) ∩ {x,y,z} := by simp [hvm]
    simpa [he] using hm
  have hwout : w ∉ ({x,y,z} : Finset α) := by
    intro hwm
    have he := hcross {u,w} (by simp [hH])
    have hm : w ∈ ({u,w} : Finset α) ∩ {x,y,z} := by simp [hwm]
    simpa [he] using hm
  refine ⟨x,y,z,u,v,w,hxy,hxz,hyz,huv,huw,hvw,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro a haA haB
    simp only [Finset.mem_insert,Finset.mem_singleton] at haB
    rcases haB with he | he | he
    · exact huout (he ▸ haA)
    · exact hvout (he ▸ haA)
    · exact hwout (he ▸ haA)
  · rw [← hD,← hH]
    exact (Finset.union_sdiff_of_subset hsubD).symm

/-- Every degree-six point in a sunflower-free triple family has a rigid link,
consisting of two triangles on six other points. -/
theorem degree_six_triple_link_two_triangles
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x : α)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hd : (F.filter (fun S => x ∈ S)).card = 6) :
    ∃ a b c d e f : α,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ d ≠ e ∧ d ≠ f ∧ e ≠ f ∧
      Disjoint ({a,b,c} : Finset α) {d,e,f} ∧
      x ∉ ({a,b,c,d,e,f} : Finset α) ∧
      Erdos20BCWConditional.residualLink F {x} =
        {{a,b},{a,c},{b,c}} ∪ {{d,e},{d,f},{e,f}} := by
  open Erdos20BCWConditional Erdos20StrictCore in
    have hc : (residualLink F {x}).card = 6 := by
      simpa [card_residualLink, upperStar] using hd
    have hul : ∀ S ∈ residualLink F {x}, S.card = 2 := by
      simpa using residualLink_uniform (core := {x}) hu
    have hfl := residualLink_sunflowerFree (core := {x}) hf
    obtain ⟨a,b,c,d,e,f,hab,hac,hbc,hde,hdf,hef,hdis,hshape⟩ :=
      six_edges_two_disjoint_triangles (residualLink F {x}) hul hfl hc
    have hx : ∀ S ∈ residualLink F {x}, x ∉ S := by
      intro S hS
      simpa using residualLink_member_disjoint_core hS
    refine ⟨a,b,c,d,e,f,hab,hac,hbc,hde,hdf,hef,hdis,?_,hshape⟩
    intro hmem
    simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
    rcases hmem with he | he | he | he | he | he
    · exact hx {a,b} (by simp [hshape]) (by simp [he])
    · exact hx {a,b} (by simp [hshape]) (by simp [he])
    · exact hx {a,c} (by simp [hshape]) (by simp [he])
    · exact hx {d,e} (by simp [hshape]) (by simp [he])
    · exact hx {d,e} (by simp [hshape]) (by simp [he])
    · exact hx {d,f} (by simp [hshape]) (by simp [he])

/-- Any edge of a triangle has its third vertex, independently of orientation. -/
theorem triangle_edge_extension
    {α : Type*} [DecidableEq α] (x y z a b : α)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hab : a ≠ b)
    (hm : ({a,b} : Finset α) ∈ ({{x,y},{x,z},{y,z}} : Finset (Finset α))) :
    ∃ c, a ≠ c ∧ b ≠ c ∧
      ({a,c} : Finset α) ∈ ({{x,y},{x,z},{y,z}} : Finset (Finset α)) ∧
      ({b,c} : Finset α) ∈ ({{x,y},{x,z},{y,z}} : Finset (Finset α)) := by
  have ha : a ∈ ({a,b} : Finset α) := by simp
  have hb : b ∈ ({a,b} : Finset α) := by simp
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with he | he | he
  · rw [he] at ha hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      subst a <;> subst b <;> simp_all [Finset.pair_comm]
    · exact ⟨z,hxz,hyz,by simp,by simp⟩
    · exact ⟨z,hyz,hxz,by simp,by simp⟩
  · rw [he] at ha hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      subst a <;> subst b <;> simp_all [Finset.pair_comm]
    · exact ⟨y,hxy,Ne.symm hyz,by simp,by simp [Finset.pair_comm]⟩
    · exact ⟨y,Ne.symm hyz,hxy,by simp [Finset.pair_comm],by simp⟩
  · rw [he] at ha hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      subst a <;> subst b <;> simp_all [Finset.pair_comm]
    · exact ⟨x,Ne.symm hxy,Ne.symm hxz,by simp [Finset.pair_comm],by simp [Finset.pair_comm]⟩
    · exact ⟨x,Ne.symm hxz,Ne.symm hxy,by simp [Finset.pair_comm],by simp [Finset.pair_comm]⟩

/-- Every edge of an extremal six-edge graph lies in a triangle. -/
theorem six_edges_edge_extension
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 2) (hf : IsSunflowerFree F 3) (hc : F.card = 6)
    (a b : α) (hm : ({a,b} : Finset α) ∈ F) :
    ∃ c, a ≠ c ∧ b ≠ c ∧ ({a,c} : Finset α) ∈ F ∧ ({b,c} : Finset α) ∈ F := by
  have hab : a ≠ b := by intro he; have := hu {a,b} hm; simp [he] at this
  obtain ⟨x,y,z,u,v,w,hxy,hxz,hyz,huv,huw,hvw,hdis,hF⟩ :=
    six_edges_two_disjoint_triangles F hu hf hc
  rw [hF] at hm ⊢
  rcases Finset.mem_union.mp hm with hm | hm
  · obtain ⟨c,hac,hbc,ha,hb⟩ := triangle_edge_extension x y z a b hxy hxz hyz hab hm
    exact ⟨c,hac,hbc,Finset.mem_union_left _ ha,Finset.mem_union_left _ hb⟩
  · obtain ⟨c,hac,hbc,ha,hb⟩ := triangle_edge_extension u v w a b huv huw hvw hab hm
    exact ⟨c,hac,hbc,Finset.mem_union_right _ ha,Finset.mem_union_right _ hb⟩

/-- Adjacent edges in an extremal graph close to a triangle. -/
theorem six_edges_adjacent_close
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 2) (hf : IsSunflowerFree F 3) (hc : F.card = 6)
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hm : ({a,b} : Finset α) ∈ F) (hn : ({a,c} : Finset α) ∈ F) :
    ({b,c} : Finset α) ∈ F := by
  obtain ⟨d,had,hbd,hadF,hbdF⟩ := six_edges_edge_extension F hu hf hc a b hm
  have hsub : ({{a,b},{a,d},{b,d}} : Finset (Finset α)) ⊆ F := by
    intro S hS
    simp only [Finset.mem_insert,Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl <;> assumption
  have hcin : ({a,c} : Finset α) ∈ ({{a,b},{a,d},{b,d}} : Finset (Finset α)) := by
    by_contra hnot
    have he := triangle_isolated F a b d hab had hbd
      (rank_two_three_petals_degree_le_two F hu hf) hsub {a,c} hn hnot
    have ha : a ∈ ({a,c} : Finset α) ∩ {a,b,d} := by simp
    simpa [he] using ha
  simp only [Finset.mem_insert,Finset.mem_singleton] at hcin
  rcases hcin with he | he | he
  · have hm' : c ∈ ({a,b} : Finset α) := by rw [← he]; simp
    simp [Ne.symm hac,Ne.symm hbc] at hm'
  · have hm' : c ∈ ({a,d} : Finset α) := by rw [← he]; simp
    have hcd : c = d := by simpa [Ne.symm hac] using hm'
    simpa [hcd] using hbdF
  · have hm' : a ∈ ({b,d} : Finset α) := by rw [← he]; simp
    simp [hab,had] at hm'

/-- Two saturated vertices of one triple force a tetrahedron boundary. -/
theorem two_degree_six_vertices_force_tetrahedron
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x y z : α)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hxyz : ({x,y,z} : Finset α) ∈ F)
    (hxdeg : (F.filter (fun S => x ∈ S)).card = 6)
    (hydeg : (F.filter (fun S => y ∈ S)).card = 6) :
    ∃ w, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ x ≠ w ∧ y ≠ w ∧ z ≠ w ∧
      ({x,y,w} : Finset α) ∈ F ∧ ({x,z,w} : Finset α) ∈ F ∧
      ({y,z,w} : Finset α) ∈ F := by
  open Erdos20BCWConditional Erdos20StrictCore in
    have hxy : x ≠ y := by
      intro he
      have hh := hu {x,y,z} hxyz
      have hc := Finset.card_pair_eq_one_or_two (a := y) (b := z)
      simp only [he,Finset.insert_idem] at hh
      omega
    have hxz : x ≠ z := by
      intro he
      have hh := hu {x,y,z} hxyz
      have hc := Finset.card_pair_eq_one_or_two (a := y) (b := z)
      have heq : ({x,y,z} : Finset α) = {y,z} := by ext t; simp [he,or_comm]
      rw [heq] at hh
      omega
    have hyz : y ≠ z := by
      intro he
      have hh := hu {x,y,z} hxyz
      have hc := Finset.card_pair_eq_one_or_two (a := x) (b := z)
      have heq : ({x,y,z} : Finset α) = {x,z} := by ext t; simp [he]
      rw [heq] at hh
      omega
    have hul (a : α) : ∀ S ∈ residualLink F {a}, S.card = 2 := by
      simpa using residualLink_uniform (core := {a}) hu
    have hfl (a : α) := residualLink_sunflowerFree (core := {a}) hf
    have hclx : (residualLink F {x}).card = 6 := by
      simpa [card_residualLink,upperStar] using hxdeg
    have hcly : (residualLink F {y}).card = 6 := by
      simpa [card_residualLink,upperStar] using hydeg
    have hmemx : ({y,z} : Finset α) ∈ residualLink F {x} := by
      apply mem_residualLink_iff.mpr
      refine ⟨{x,y,z},hxyz,by simp,?_⟩
      ext a
      simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton]
      grind
    obtain ⟨w,hyw,hzw,hywL,hzwL⟩ := six_edges_edge_extension
      (residualLink F {x}) (hul x) (hfl x) hclx y z hmemx
    have hxw : x ≠ w := by
      have hd := residualLink_member_disjoint_core hywL
      have hxn : x ∉ ({y,w} : Finset α) := Finset.disjoint_left.mp hd (by simp)
      intro he; exact hxn (by simp [he])
    have hxyw : ({x,y,w} : Finset α) ∈ F := by
      have he : ({y,w} : Finset α) ∪ {x} = {x,y,w} := by ext t; simp
      simpa only [he] using core_union_residual_mem_family hywL
    have hxzw : ({x,z,w} : Finset α) ∈ F := by
      have he : ({z,w} : Finset α) ∪ {x} = {x,z,w} := by ext t; simp
      simpa only [he] using core_union_residual_mem_family hzwL
    have hxzL : ({x,z} : Finset α) ∈ residualLink F {y} := by
      apply mem_residualLink_iff.mpr
      refine ⟨{x,y,z},hxyz,by simp,?_⟩
      ext a
      simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton]
      grind
    have hxwL : ({x,w} : Finset α) ∈ residualLink F {y} := by
      apply mem_residualLink_iff.mpr
      refine ⟨{x,y,w},hxyw,by simp,?_⟩
      ext a
      simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton]
      grind
    have hzwL' := six_edges_adjacent_close (residualLink F {y}) (hul y) (hfl y) hcly
      x z w hxz hxw hzw hxzL hxwL
    have hyzw : ({y,z,w} : Finset α) ∈ F := by
      have he : ({z,w} : Finset α) ∪ {y} = {y,z,w} := by ext t; simp
      simpa only [he] using core_union_residual_mem_family hzwL'
    exact ⟨w,hxy,hxz,hyz,hxw,hyw,hzw,hxyw,hxzw,hyzw⟩

end Erdos20GraphEquality
