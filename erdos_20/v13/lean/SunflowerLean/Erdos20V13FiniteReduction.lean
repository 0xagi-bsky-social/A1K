import SunflowerLean.Erdos20FiniteReduction
import SunflowerLean.Erdos20V8Targets

namespace Erdos20V13FiniteReduction
open Erdos20BCWConditional Erdos20FiniteReduction Erdos20V8Targets
universe u v

/-- Intersectingness includes S=T and is invariant under injective relabelling. -/
theorem intersecting_mapFamily_iff
    {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (F : Finset (Finset α)) :
    (∀ S ∈ mapFamily e F, ∀ T ∈ mapFamily e F, (S ∩ T).Nonempty) ↔
    (∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) := by
  constructor
  · intro hi S hS T hT
    have h := hi (S.map e) (Finset.mem_map.mpr ⟨S,hS,rfl⟩)
      (T.map e) (Finset.mem_map.mpr ⟨T,hT,rfl⟩)
    rw [← Finset.map_inter] at h
    exact Finset.map_nonempty.mp h
  · intro hi S hS T hT
    obtain ⟨S',hS',rfl⟩ := Finset.mem_map.mp hS
    obtain ⟨T',hT',rfl⟩ := Finset.mem_map.mp hT
    change ((S'.map e) ∩ (T'.map e)).Nonempty
    rw [← Finset.map_inter]
    exact Finset.map_nonempty.mpr (hi S' hS' T' hT')

/-- The inherited support relabelling construction with intersectingness retained.
No ambient finiteness or small-universe assumption is needed. -/
theorem exists_intersecting_fin_relabel
    {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (n r p : ℕ)
    (hsupport : (support F).card ≤ n)
    (hu : ∀ S ∈ F, S.card=r) (hf : IsSunflowerFree F p)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) :
    ∃ G : Finset (Finset (Fin n)), G.card=F.card ∧
      (∀ S ∈ G, S.card=r) ∧ IsSunflowerFree G p ∧
      (∀ S ∈ G, ∀ T ∈ G, (S ∩ T).Nonempty) := by
  classical
  let ambient := support F
  let restricted : Finset (Finset ambient) := F.image (restrictSet ambient)
  let forget : ambient ↪ α := Function.Embedding.subtype _
  have hrecover : mapFamily forget restricted=F := by
    unfold mapFamily restricted
    rw [Finset.map_eq_image,Finset.image_image]
    calc
      _ = F.image id := Finset.image_congr (by
        intro S hS
        exact map_restrictSet ambient S (member_subset_support hS))
      _ = F := Finset.image_id
  have hrcard : restricted.card=F.card := by
    rw [← card_mapFamily forget restricted,hrecover]
  have hru : ∀ S ∈ restricted, S.card=r := by
    intro S hS
    have hmem : S.map forget ∈ F := by
      rw [← hrecover]
      exact Finset.mem_map.mpr ⟨S,hS,rfl⟩
    simpa using hu (S.map forget) hmem
  have hrf : IsSunflowerFree restricted p :=
    (isSunflowerFree_mapFamily_iff forget restricted p).mp (by simpa [hrecover] using hf)
  have hri : ∀ S ∈ restricted, ∀ T ∈ restricted, (S ∩ T).Nonempty :=
    (intersecting_mapFamily_iff forget restricted).mp (by simpa [hrecover] using hi)
  let number : ambient ≃ Fin ambient.card :=
    (Fintype.equivFin ambient).trans (finCongr (Fintype.card_coe ambient))
  let embed : ambient ↪ Fin n := number.toEmbedding.trans (Fin.castLEEmb hsupport)
  refine ⟨mapFamily embed restricted,?_,uniform_mapFamily embed restricted r hru,
    (isSunflowerFree_mapFamily_iff embed restricted p).mpr hrf,
    (intersecting_mapFamily_iff embed restricted).mpr hri⟩
  simpa using hrcard

/-- An intersecting 28-member rank-four family has support at most 85.
Each of the 27 nonanchor members contributes at most three new vertices. -/
theorem intersecting_twenty_eight_support_le_eighty_five
    {α : Type u} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card=4) (hc : F.card=28)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) :
    (support F).card≤85 := by
  classical
  obtain ⟨R,hR⟩ := Finset.card_pos.mp (show 0<F.card by omega)
  have hdiff (S : Finset α) (hS : S ∈ F.erase R) : (S \ R).card≤3 := by
    have hSF := Finset.mem_of_mem_erase hS
    have hpos := (hi S hSF R hR).card_pos
    have he := Finset.card_sdiff_add_card_inter S R
    have hSc := hu S hSF
    omega
  have hcover : support F ⊆ R ∪ (F.erase R).biUnion (fun S => S \ R) := by
    intro x hx
    obtain ⟨S,hS,hxS⟩ := Finset.mem_biUnion.mp hx
    by_cases hxR : x ∈ R
    · exact Finset.mem_union_left _ hxR
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨S,Finset.mem_erase.mpr ⟨?_,hS⟩,Finset.mem_sdiff.mpr ⟨hxS,hxR⟩⟩
      intro he
      exact hxR (he ▸ hxS)
  have hb := Finset.card_biUnion_le_card_mul (F.erase R) (fun S => S \ R) 3 hdiff
  have herase := Finset.card_erase_of_mem hR
  have hRc := hu R hR
  have hc1 := Finset.card_le_card hcover
  have hc2 := Finset.card_union_le R ((F.erase R).biUnion (fun S => S \ R))
  omega

/-- A finite exact-size obstruction to I27, with all semantic constraints retained. -/
def FiniteIntersectingObstruction : Prop :=
  ∃ G : Finset (Finset (Fin 85)), G.card=28 ∧
    (∀ S ∈ G, S.card=4) ∧ IsSunflowerFree G 3 ∧
    (∀ S ∈ G, ∀ T ∈ G, (S ∩ T).Nonempty)

/-- Every larger intersecting family yields a 28-member Fin85 obstruction. -/
theorem finite_obstruction_of_intersecting_counterexample
    {α : Type u} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card=4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) (hc : 27<F.card) :
    FiniteIntersectingObstruction := by
  obtain ⟨H,hsub,hcard⟩ := Finset.exists_subset_card_eq (show 28≤F.card by omega)
  have hHu : ∀ S ∈ H, S.card=4 := fun S hS => hu S (hsub hS)
  have hHf : IsSunflowerFree H 3 := fun G hG => hf G (hG.trans hsub)
  have hHi : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty :=
    fun S hS T hT => hi S (hsub hS) T (hsub hT)
  have hs := intersecting_twenty_eight_support_le_eighty_five H hHu hcard hHi
  obtain ⟨G,hGc,hGu,hGf,hGi⟩ := exists_intersecting_fin_relabel H 85 4 3 hs hHu hHf hHi
  exact ⟨G,hGc.trans hcard,hGu,hGf,hGi⟩

/-- I27 is equivalent to absence of the exact finite obstruction.
This does not execute the enormous finite search. -/
theorem intersecting_upper_twenty_seven_iff_no_finite_obstruction :
    IntersectingRankFourUpper 27 ↔ ¬ FiniteIntersectingObstruction := by
  constructor
  · intro hI hobs
    obtain ⟨G,hc,hu,hf,hi⟩ := hobs
    have hb := hI G hu hf hi
    omega
  · intro hn α inst F hu hf hi
    by_contra hnot
    exact hn (finite_obstruction_of_intersecting_counterexample F hu hf hi (by omega))

/-- The finite reduction also transports I27 to every universe. -/
theorem intersecting_upper_twenty_seven_large_universe
    (hI : IntersectingRankFourUpper 27)
    {α : Type u} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ S ∈ F, S.card=4) (hf : IsSunflowerFree F 3)
    (hi : ∀ S ∈ F, ∀ T ∈ F, (S ∩ T).Nonempty) : F.card≤27 := by
  by_contra hnot
  exact intersecting_upper_twenty_seven_iff_no_finite_obstruction.mp hI
    (finite_obstruction_of_intersecting_counterexample F hu hf hi (by omega))

end Erdos20V13FiniteReduction
