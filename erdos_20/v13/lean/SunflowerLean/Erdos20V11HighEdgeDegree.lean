import SunflowerLean.Erdos20V11HighEdgeReserve
import SunflowerLean.Erdos20V11HighEdgeCounts
import SunflowerLean.Erdos20V11EdgeCapacityThree

namespace Erdos20V11HighEdgeDegree
open Erdos20BCWConditional Erdos20StrictCore Erdos20Incidence Erdos20V8Boundary
open Erdos20V9HighGraph Erdos20V10HighTriangle Erdos20DesignNormalForm
open Erdos20V9HighCompatibility Erdos20V5Frontier Erdos20V11EdgeTrace Erdos20V11EdgePairs
open Erdos20V11HighEdgeReserve Erdos20V11HighEdgeCounts Erdos20V11EdgeCapacityThree
open Erdos20DegreeCongruences

/-- Every one of the five residual points of a high edge has degree at most
fourteen. Eight endpoint incidences and at most six further admissible-pair
incidences are counted in the actual original family. -/
theorem high_edge_residual_point_degree_le_fourteen {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) (y : α) (hy : y ∈ highNeighbors F x)
    (u : α) (huU : u ∈ edgeSupport F x y) : degree F u ≤ 14 := by
  classical
  have hxy : x ≠ y := ((mem_highNeighbors_iff F x y).mp hy).2.1.symm
  obtain ⟨A,hAL,hyA,hAc,hAu,hAf,hAi,hiso⟩ := component_at_high_neighbor F hu hf x hx y hy
  have heU := edgeSupport_eq_component_erase F x y hxy A hAL hyA hAc hAu hAf hAi hiso
  obtain ⟨e,he⟩ := ten_isomorphic_canonical A hAu hAf hAi hAc
  change A = D.image (fun P => P.image e) at he
  have hAS : support A ⊆ Finset.univ.image e := by
    intro v hvA
    obtain ⟨P,hP,hvP⟩ := Finset.mem_biUnion.mp hvA
    rw [he] at hP
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hvP
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
  have heS : support A = Finset.univ.image e := by
    apply Finset.eq_of_subset_of_card_le hAS
    rw [Finset.card_image_of_injective _ e.injective,
      (intersecting_ten_design A hAu hAf hAi hAc).1]
    decide
  have huA : u ∈ support A := by rw [heU] at huU; exact (Finset.mem_erase.mp huU).2
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (hAS hyA)
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (hAS huA)
  have hab : a ≠ b := by
    intro hab
    have h := (mem_edgeSupport_iff F x (e a) (e b)).mp huU
    exact h.2.1 (by rw [hab])
  let E := F.filter (fun R => x ∈ R ∨ e a ∈ R)
  let PP := (allowedPairs a b).image (fun C => C.image e)
  have hEF : E ⊆ F := Finset.filter_subset _ _
  have hinside : degree E (e b) ≤ 8 := by
    have hei : E.filter (fun R => e b ∈ R) =
        F.filter (fun R => e b ∈ R ∧ (x ∈ R ∨ e a ∈ R)) := by
      ext R
      simp only [E,Finset.mem_filter]
      tauto
    change (E.filter (fun R => e b ∈ R)).card ≤ 8
    rw [hei,high_edge_residual_point_inside_card_eight F hu hf x hx (e a) hy (e b) huU]
  have hPP : PP.card ≤ 2 := by
    exact (Finset.card_image_le).trans (by rw [allowedPairs_card a b hab])
  apply degree_le_fourteen_of_three_reserved_pairs F E PP (e b) hEF hinside hPP
  · intro R hR hubR
    obtain ⟨hRF,hRE⟩ := Finset.mem_sdiff.mp hR
    have hxR : x ∉ R := fun h => hRE (Finset.mem_filter.mpr ⟨hRF,Or.inl h⟩)
    have hyR : e a ∉ R := fun h => hRE (Finset.mem_filter.mpr ⟨hRF,Or.inr h⟩)
    let T : Finset (Fin 6) := Finset.univ.filter (fun i => e i ∈ R)
    have hbT : b ∈ T := by simpa [T] using hubR
    have haT : a ∉ T := by simpa [T] using hyR
    have htrace : R ∩ edgeSupport F x (e a) = T.image e := by
      rw [heU,heS]
      ext v
      simp only [Finset.mem_inter,Finset.mem_erase,Finset.mem_image,
        Finset.mem_univ,true_and,T,Finset.mem_filter]
      constructor
      · rintro ⟨hvR,hva,i,rfl⟩
        exact ⟨i,hvR,rfl⟩
      · rintro ⟨i,hi,rfl⟩
        refine ⟨hi,?_,i,rfl⟩
        intro hia
        exact hyR (hia ▸ hi)
    have hcard : (R ∩ edgeSupport F x (e a)).card=T.card := by
      rw [htrace,Finset.card_image_of_injective _ e.injective]
    have ht := high_edge_member_trace_zero_or_two F hu hf x hx (e a) hy R hRF hxR hyR
    have hpos : 0<T.card := Finset.card_pos.mpr ⟨b,hbT⟩
    have hT2 : T.card=2 := by omega
    have hcycle := original_trace_is_cycle_of_card_two F hu hf x hx (e a) hy
      A hAL heU e he a rfl R hRF hxR hyR hT2
    have hTP : T ∈ allowedPairs a b := Finset.mem_filter.mpr
      ⟨Finset.mem_univ T,hT2,haT,hbT,hcycle⟩
    refine ⟨T.image e,Finset.mem_image.mpr ⟨T,hTP,rfl⟩,?_⟩
    intro v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hi).2
  · intro C hC
    obtain ⟨D0,hD0,hDC⟩ := Finset.mem_image.mp hC
    rw [← hDC]
    exact allowed_pair_three_reserved_members F hu hf x hx (e a) hy A hAL heU e he a b rfl D0 hD0
  · intro C hC
    obtain ⟨D0,hD0,hDC⟩ := Finset.mem_image.mp hC
    rw [← hDC]
    exact allowed_pair_star_card_le_six F hu hf e a b D0 hD0

/-- A family with minimum supported degree fifteen has no adjacent high points.
In particular the boundary regime with minimum degree seventeen has none. -/
theorem no_high_edge_of_min_degree_fifteen {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (hu : ∀ R ∈ F, R.card=4) (hf : IsSunflowerFree F 3)
    (hmin : ∀ u ∈ support F, 15 ≤ degree F u)
    (x : α) (hx : x ∈ highPoints F) (y : α) (hy : y ∈ highNeighbors F x) : False := by
  have hc := high_edge_support_card_five F hu hf x hx y hy
  obtain ⟨u,huU⟩ := Finset.card_pos.mp (show 0<(edgeSupport F x y).card by omega)
  have hlow := high_edge_residual_point_degree_le_fourteen F hu hf x hx y hy u huU
  have hs : u ∈ support F := Erdos20V8HighWeights.residual_support_subset F {x,y} huU
  have hh := hmin u hs
  omega

end Erdos20V11HighEdgeDegree
