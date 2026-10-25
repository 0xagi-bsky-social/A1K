import SunflowerLean.Erdos20RankThreeEven
import Mathlib.Combinatorics.SimpleGraph.FiveWheelLike

/-! Disjointness graphs and tetrahedron counting for the sharp triple bound.
The final assembly is in `Erdos20SharpTwenty`. -/
namespace Erdos20SharpTriples
open Erdos20BCWConditional Erdos20Incidence Erdos20RankThree Erdos20RankThreeEven

/-- Retaining the exact disjoint count makes the degree-sensitive trace bound stronger. -/
theorem rank_three_card_le_degree_disjoint_add_seven
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (R : Finset α) (x : α) (hR : R ∈ F) (hx : x ∈ R)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) :
    F.card ≤ (F.filter (fun S => x ∈ S)).card +
      (F.filter (fun S => S ∩ R = ∅)).card + 7 := by
  classical
  let A := F.filter (fun S => x ∈ S)
  let D := F.filter (fun S => S ∩ R = ∅)
  let P := exactTrace F R (R.erase x)
  let Q := (R.erase x).biUnion (fun y => exactTrace F R {y})
  have hcover : F ⊆ (A ∪ D) ∪ (P ∪ Q) := by
    intro S hS
    by_cases hxS : x ∈ S
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hS,hxS⟩))
    · by_cases he : S ∩ R = ∅
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hS,he⟩))
      · have hproper : S ∩ R ≠ R := by
          intro heq
          have : x ∈ S ∩ R := by rw [heq]; exact hx
          exact hxS (Finset.mem_inter.mp this).1
        obtain ⟨y, hyR, hcase⟩ := nonempty_proper_subset_triple R (S ∩ R)
          (hu R hR) Finset.inter_subset_right (Finset.nonempty_iff_ne_empty.mpr he) hproper
        apply Finset.mem_union_right
        rcases hcase with hsingle | hpair
        · apply Finset.mem_union_right
          apply Finset.mem_biUnion.mpr
          have hyx : y ≠ x := by
            intro heq
            have : x ∈ S ∩ R := by rw [hsingle, heq]; simp
            exact hxS (Finset.mem_inter.mp this).1
          exact ⟨y, Finset.mem_erase.mpr ⟨hyx, hyR⟩, Finset.mem_filter.mpr ⟨hS, hsingle⟩⟩
        · apply Finset.mem_union_left
          have hyx : y = x := by
            by_contra hne
            have : x ∈ S ∩ R := by rw [hpair]; exact Finset.mem_erase.mpr ⟨Ne.symm hne,hx⟩
            exact hxS (Finset.mem_inter.mp this).1
          exact Finset.mem_filter.mpr ⟨hS, by simpa [hyx] using hpair⟩
  have hP : P.card ≤ 1 := pair_trace_card_le_one F R (R.erase x) hR hu hf
    (Finset.erase_subset _ _) (by rw [Finset.card_erase_of_mem hx, hu R hR])
  have hQ : Q.card ≤ 6 := by
    calc
      _ ≤ ∑ y ∈ R.erase x, (exactTrace F R {y}).card := Finset.card_biUnion_le
      _ ≤ ∑ _y ∈ R.erase x, 3 := Finset.sum_le_sum
        (fun y _ => singleton_trace_card_le_three F R {y} hR hu hf (by simp))
      _ = 6 := by simp [Finset.card_erase_of_mem hx, hu R hR]
  have h1 := Finset.card_le_card hcover
  have h2 := Finset.card_union_le (A ∪ D) (P ∪ Q)
  have h3 := Finset.card_union_le A D
  have h4 := Finset.card_union_le P Q
  change F.card ≤ A.card + D.card + 7
  omega

/-- The graph joining distinct disjoint members of the family. -/
def disjointnessGraph {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : SimpleGraph F where
  Adj S T := S ≠ T ∧ S.val ∩ T.val = ∅
  symm := by
    intro S T h
    exact ⟨h.1.symm, by simpa [Finset.inter_comm] using h.2⟩
  loopless := by intro S; simp

instance disjointnessGraph_decidableAdj {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : DecidableRel (disjointnessGraph F).Adj :=
  fun S T => inferInstanceAs (Decidable (S ≠ T ∧ S.val ∩ T.val = ∅))

/-- A triangle in the disjointness graph is an empty-core three-sunflower. -/
theorem disjointnessGraph_triangle_free {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hf : IsSunflowerFree F 3) :
    (disjointnessGraph F).CliqueFree 3 := by
  classical
  intro K hK
  obtain ⟨S, T, U, hST, hSU, hTU, _⟩ := SimpleGraph.is3Clique_iff.mp hK
  have hST' : S.val ≠ T.val := fun h => hST.1 (Subtype.ext h)
  have hSU' : S.val ≠ U.val := fun h => hSU.1 (Subtype.ext h)
  have hTU' : T.val ≠ U.val := fun h => hTU.1 (Subtype.ext h)
  apply hf {S.val, T.val, U.val}
  · intro R hR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl | rfl
    · exact S.property
    · exact T.property
    · exact U.property
  · exact Erdos20RankThree.sunflower_three_of_intersections _ _ _ _
      hST' hSU' hTU' hST.2 hSU.2 hTU.2

/-- Graph degrees equal the number of members disjoint from the anchor. -/
theorem disjointnessGraph_degree_eq {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ S ∈ F, S.card = 3) (R : F) :
    (disjointnessGraph F).degree R = (F.filter (fun S => S ∩ R.val = ∅)).card := by
  classical
  rw [SimpleGraph.degree]
  have he : ((disjointnessGraph F).neighborFinset R).image Subtype.val =
      F.filter (fun S => S ∩ R.val = ∅) := by
    ext S
    simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset, Finset.mem_filter]
    constructor
    · rintro ⟨T, hT, rfl⟩
      exact ⟨T.property, by simpa [Finset.inter_comm] using hT.2⟩
    · rintro ⟨hSF, hi⟩
      refine ⟨⟨S,hSF⟩, ?_, rfl⟩
      change R ≠ ⟨S,hSF⟩ ∧ R.val ∩ S = ∅
      refine ⟨?_, by simpa [Finset.inter_comm] using hi⟩
      intro heq
      have hev : R.val = S := congrArg Subtype.val heq
      have hzero : S = ∅ := by simpa [hev] using hi
      have hc := hu S hSF
      simp [hzero] at hc
  rw [← he, Finset.card_image_of_injective _ Subtype.val_injective]

/-- The thirteen-member meeting bound gives a graph minimum-degree bound. -/
theorem disjointnessGraph_degree_add_thirteen_ge
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) (R : F) :
    F.card ≤ (disjointnessGraph F).degree R + 13 := by
  classical
  rw [disjointnessGraph_degree_eq F hu R]
  have hmeet := Erdos20RankThree.meeting_neighborhood_card_le_thirteen F R.val R.property hu hf
  have hs := Finset.filter_card_add_filter_neg_card_eq_card
    (s := F) (p := fun S => (S ∩ R.val).Nonempty)
  simp only [Finset.not_nonempty_iff_eq_empty] at hs
  omega

/-- A two-coloring partitions the family into two intersecting classes. -/
theorem card_le_twenty_of_disjointnessGraph_two_colorable
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hcol : (disjointnessGraph F).Colorable 2) : F.card ≤ 20 := by
  classical
  obtain ⟨c⟩ := hcol
  let classes : Fin 2 → Finset (Finset α) := fun i =>
    (Finset.univ.filter (fun S : F => c S = i)).image Subtype.val
  have hmem : ∀ i S, S ∈ classes i ↔ ∃ hS : S ∈ F, c ⟨S,hS⟩ = i := by
    intro i S
    simp only [classes, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨T, hi, rfl⟩
      exact ⟨T.property, hi⟩
    · rintro ⟨hS, hi⟩
      exact ⟨⟨S,hS⟩, hi, rfl⟩
  have hsub : ∀ i, classes i ⊆ F := by
    intro i S hS
    exact ((hmem i S).mp hS).choose
  have hcap : ∀ i, (classes i).card ≤ 10 := by
    intro i
    apply Erdos20RankThree.intersecting_rank_three_card_le_ten _
      (fun S hS => hu S (hsub i hS))
      (fun H hH hsun => hf H (hH.trans (hsub i)) hsun)
    intro S hS T hT
    obtain ⟨hSF, hcS⟩ := (hmem i S).mp hS
    obtain ⟨hTF, hcT⟩ := (hmem i T).mp hT
    by_contra hnot
    have hi : S ∩ T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    have hne : (⟨S,hSF⟩ : F) ≠ ⟨T,hTF⟩ := by
      intro heq
      have hv : S = T := congrArg Subtype.val heq
      have he : S = ∅ := by simpa [← hv] using hi
      have hs3 := hu S hSF
      simp [he] at hs3
    exact c.valid (show (disjointnessGraph F).Adj ⟨S,hSF⟩ ⟨T,hTF⟩ from ⟨hne,hi⟩)
      (hcS.trans hcT.symm)
  have hcover : F ⊆ Finset.univ.biUnion classes := by
    intro S hS
    exact Finset.mem_biUnion.mpr ⟨c ⟨S,hS⟩, Finset.mem_univ _,
      (hmem _ S).mpr ⟨hS,rfl⟩⟩
  calc
    _ ≤ (Finset.univ.biUnion classes).card := Finset.card_le_card hcover
    _ ≤ ∑ i, (classes i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin 2, 10 := Finset.sum_le_sum (fun i _ => hcap i)
    _ = 20 := by simp

/-- Andrasfai--Erdos--Sos excludes twenty-two members: the disjointness
 graph would be triangle-free with minimum degree at least nine, hence bipartite. -/
theorem rank_three_three_petals_card_le_twenty_one
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3) : F.card ≤ 21 := by
  classical
  have hb := rank_three_three_petals_card_le_twenty_two F hu hf
  by_contra hnot
  have hc : F.card = 22 := by omega
  have hne : F.Nonempty := Finset.card_pos.mp (by omega)
  letI : Nonempty F := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  have hmin : 9 ≤ (disjointnessGraph F).minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro R
    have h := disjointnessGraph_degree_add_thirteen_ge F hu hf R
    omega
  have hcol : (disjointnessGraph F).Colorable 2 := by
    apply SimpleGraph.colorable_of_cliqueFree_lt_minDegree
      (disjointnessGraph_triangle_free F hf)
    have hcard : Fintype.card F = 22 := by simpa using hc
    simp only [hcard]
    omega
  have h20 := card_le_twenty_of_disjointnessGraph_two_colorable F hu hf hcol
  omega

/-- A low-degree point in each member forces the sharp bound twenty.
This isolates the remaining case into triples whose points all have degree six. -/
theorem rank_three_card_le_twenty_of_each_member_low_degree
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hlow : ∀ R ∈ F, ∃ x ∈ R, (F.filter (fun S => x ∈ S)).card ≤ 5) :
    F.card ≤ 20 := by
  classical
  have hb := rank_three_three_petals_card_le_twenty_one F hu hf
  by_contra hnot
  have hc : F.card = 21 := by omega
  have hne : F.Nonempty := Finset.card_pos.mp (by omega)
  letI : Nonempty F := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  have hmin : 9 ≤ (disjointnessGraph F).minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro R
    obtain ⟨x,hxR,hd⟩ := hlow R.val R.property
    have h := rank_three_card_le_degree_disjoint_add_seven F R.val x R.property hxR hu hf
    rw [← disjointnessGraph_degree_eq F hu R] at h
    omega
  have hcol : (disjointnessGraph F).Colorable 2 := by
    apply SimpleGraph.colorable_of_cliqueFree_lt_minDegree
      (disjointnessGraph_triangle_free F hf)
    have hcard : Fintype.card F = 21 := by simpa using hc
    simp only [hcard]
    omega
  have h20 := card_le_twenty_of_disjointnessGraph_two_colorable F hu hf hcol
  omega

/-- Every twenty-one-member candidate contains a triple of degree-six points. -/
theorem card_twenty_one_exists_all_degree_six_member
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hc : F.card = 21) :
    ∃ R ∈ F, ∀ x ∈ R, (F.filter (fun S => x ∈ S)).card = 6 := by
  classical
  by_contra hnot
  push_neg at hnot
  have hlow : ∀ R ∈ F, ∃ x ∈ R, (F.filter (fun S => x ∈ S)).card ≤ 5 := by
    intro R hR
    obtain ⟨x,hx,he⟩ := hnot R hR
    have hd := rank_three_degree_le_six F hu hf x
    exact ⟨x,hx,by omega⟩
  have hb := rank_three_card_le_twenty_of_each_member_low_degree F hu hf hlow
  omega

/-- Four tetrahedron faces consume eight units of incidence excess.
Consequently at most sixteen members meet the four vertices. -/
theorem tetrahedron_meeting_card_le_sixteen
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (K : Finset α)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hK : K.card = 4) (hfaces : K.powersetCard 3 ⊆ F) :
    (F.filter (fun S => (S ∩ K).Nonempty)).card ≤ 16 := by
  classical
  let N := F.filter (fun S => (S ∩ K).Nonempty)
  have hsubN : K.powersetCard 3 ⊆ N := by
    intro S hS
    obtain ⟨hSK,hS3⟩ := Finset.mem_powersetCard.mp hS
    apply Finset.mem_filter.mpr
    refine ⟨hfaces hS, ?_⟩
    rw [Finset.inter_eq_left.mpr hSK]
    exact Finset.card_pos.mp (by omega)
  have hinc := incidence_defect_lower_bound N (K.powersetCard 3) K 3 hsubN
    (fun S hS => (Finset.mem_powersetCard.mp hS).2)
    (fun S hS => (Finset.mem_powersetCard.mp hS).1)
    (fun S hS => (Finset.mem_filter.mp hS).2)
  have hcfaces : (K.powersetCard 3).card = 4 := by
    rw [Finset.card_powersetCard, hK]
    decide
  have hdegree : ∀ x, (N.filter (fun S => x ∈ S)).card ≤ 6 := by
    intro x
    apply (Finset.card_le_card ?_).trans (rank_three_degree_le_six F hu hf x)
    intro S hS
    obtain ⟨hSN,hxS⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hSN).1,hxS⟩
  have hsum : (∑ x ∈ K, (N.filter (fun S => x ∈ S)).card) ≤ 24 := by
    calc
      _ ≤ ∑ _x ∈ K, 6 := Finset.sum_le_sum (fun x _ => hdegree x)
      _ = 24 := by simp [hK]
  change N.card ≤ 16
  rw [hcfaces] at hinc
  omega

/-- The final counting step once a tetrahedron and its small disjoint class
have been certified. -/
theorem card_le_nineteen_of_tetrahedron_disjoint_card_le_three
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (K : Finset α)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hK : K.card = 4) (hfaces : K.powersetCard 3 ⊆ F)
    (hD : (F.filter (fun S => S ∩ K = ∅)).card ≤ 3) : F.card ≤ 19 := by
  have hN := tetrahedron_meeting_card_le_sixteen F K hu hf hK hfaces
  have hs := Finset.filter_card_add_filter_neg_card_eq_card
    (s := F) (p := fun S => (S ∩ K).Nonempty)
  simp only [Finset.not_nonempty_iff_eq_empty] at hs
  omega

/-- If each pair of a triangle has an extension outside a subfamily, that
subfamily can contain at most one further extension per pair. -/
theorem triangle_pair_cover_card_le_three
    {α : Type*} [DecidableEq α] (F D : Finset (Finset α)) (A : Finset α)
    (hu : ∀ S ∈ F, S.card = 3) (hf : IsSunflowerFree F 3)
    (hDF : D ⊆ F) (hA : A.card = 3)
    (hcover : ∀ S ∈ D, ∃ C ∈ A.powersetCard 2, C ⊆ S)
    (hother : ∀ C ∈ A.powersetCard 2, ∃ T ∈ F, T ∉ D ∧ C ⊆ T) :
    D.card ≤ 3 := by
  classical
  have hcap : ∀ C ∈ A.powersetCard 2, (upperStar D C).card ≤ 1 := by
    intro C hC
    obtain ⟨T,hTF,hTD,hCT⟩ := hother C hC
    have hnot : T ∉ upperStar D C := by
      intro ht
      exact hTD (mem_upperStar_iff.mp ht).1
    have hs : insert T (upperStar D C) ⊆ Erdos20Research.extensionStar F C := by
      intro S hS
      apply Erdos20Research.mem_extensionStar_iff.mpr
      rcases Finset.mem_insert.mp hS with rfl | hS
      · exact ⟨hTF,hCT⟩
      · obtain ⟨hSD,hCS⟩ := mem_upperStar_iff.mp hS
        exact ⟨hDF hSD,hCS⟩
    have hlo := Finset.card_le_card hs
    rw [Finset.card_insert_of_notMem hnot] at hlo
    have hC2 := (Finset.mem_powersetCard.mp hC).2
    have hhi := Erdos20Research.extensionStar_card_lt F C 3 3 hu hf (by omega)
    omega
  have hs : D ⊆ (A.powersetCard 2).biUnion (upperStar D) := by
    intro S hS
    obtain ⟨C,hCA,hCS⟩ := hcover S hS
    exact Finset.mem_biUnion.mpr ⟨C,hCA,mem_upperStar_iff.mpr ⟨hS,hCS⟩⟩
  calc
    _ ≤ ((A.powersetCard 2).biUnion (upperStar D)).card := Finset.card_le_card hs
    _ ≤ ∑ C ∈ A.powersetCard 2, (upperStar D C).card := Finset.card_biUnion_le
    _ ≤ ∑ _C ∈ A.powersetCard 2, 1 := Finset.sum_le_sum hcap
    _ = 3 := by simp [Finset.card_powersetCard, hA]

/-- A set meeting all three edges of a triangle contains one of those edges. -/
theorem contains_pair_of_meets_every_pair_of_triple
    {α : Type*} [DecidableEq α] (A S : Finset α) (hA : A.card = 3)
    (hhit : ∀ C ∈ A.powersetCard 2, (S ∩ C).Nonempty) :
    ∃ C ∈ A.powersetCard 2, C ⊆ S := by
  have hi : 2 ≤ (A ∩ S).card := by
    by_contra hn
    have hdiff : 2 ≤ (A \ S).card := by
      rw [Finset.card_sdiff, Finset.inter_comm S A]
      omega
    obtain ⟨C,hCsub,hC2⟩ := Finset.exists_subset_card_eq hdiff
    have hCA : C ∈ A.powersetCard 2 := Finset.mem_powersetCard.mpr
      ⟨hCsub.trans Finset.sdiff_subset,hC2⟩
    obtain ⟨x,hx⟩ := hhit C hCA
    obtain ⟨hxS,hxC⟩ := Finset.mem_inter.mp hx
    exact (Finset.mem_sdiff.mp (hCsub hxC)).2 hxS
  obtain ⟨C,hCsub,hC2⟩ := Finset.exists_subset_card_eq hi
  exact ⟨C,Finset.mem_powersetCard.mpr ⟨hCsub.trans Finset.inter_subset_left,hC2⟩,
    hCsub.trans Finset.inter_subset_right⟩

/-- Four named distinct vertices give exactly the four named triple faces. -/
theorem tetrahedron_faces_subset_of_four_members
    {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x y z w : α)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w)
    (hxyz : ({x,y,z} : Finset α) ∈ F) (hxyw : ({x,y,w} : Finset α) ∈ F)
    (hxzw : ({x,z,w} : Finset α) ∈ F) (hyzw : ({y,z,w} : Finset α) ∈ F) :
    ({x,y,z,w} : Finset α).powersetCard 3 ⊆ F := by
  intro S hS
  obtain ⟨hsub,hS3⟩ := Finset.mem_powersetCard.mp hS
  have hK4 : ({x,y,z,w} : Finset α).card = 4 := by
    simp [hxy,hxz,hxw,hyz,hyw,hzw]
  have hstrict : S ⊂ ({x,y,z,w} : Finset α) :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub,by intro he; rw [he,hK4] at hS3; omega⟩
  obtain ⟨v,hv,hSv⟩ := Finset.ssubset_iff_exists_subset_erase.mp hstrict
  have he : S = ({x,y,z,w} : Finset α).erase v := Finset.eq_of_subset_of_card_le hSv (by
    rw [Finset.card_erase_of_mem hv,hK4,hS3])
  rw [he]
  simp only [Finset.mem_insert,Finset.mem_singleton] at hv
  rcases hv with hv | hv | hv | hv <;> subst v
  · have heq : ({x,y,z,w} : Finset α).erase x = {y,z,w} := by
      ext t
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      grind
    simpa only [heq] using hyzw
  · have heq : ({x,y,z,w} : Finset α).erase y = {x,z,w} := by
      ext t
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      grind
    simpa only [heq] using hxzw
  · have heq : ({x,y,z,w} : Finset α).erase z = {x,y,w} := by
      ext t
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      grind
    simpa only [heq] using hxyw
  · have heq : ({x,y,z,w} : Finset α).erase w = {x,y,z} := by
      ext t
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      grind
    simpa only [heq] using hxyz

end Erdos20SharpTriples
