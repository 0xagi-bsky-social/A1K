import ProfileAFiberBound
import UniqueDesignTails

namespace FrontierGenericHeavyExtensions
open Erdos20BCWConditional Erdos20StrictCore Erdos20V5Frontier
open Erdos20Incidence FrontierProfileAFiberBound

variable {α : Type*} [DecidableEq α]

def extensions (D : Finset (Finset α)) (P : Finset α) : Finset α :=
  (support D).filter (fun a => a ∉ P ∧ insert a P ∈ D)

lemma extensions_card_two (D : Finset (Finset α))
    (hu : ∀ T ∈ D, T.card = 3) (hf : IsSunflowerFree D 3)
    (hi : ∀ T ∈ D, ∀ U ∈ D, (T ∩ U).Nonempty) (hc : D.card = 10)
    (P : Finset α) (hP : P.card = 2) (hPS : P ⊆ support D) :
    (extensions D P).card = 2 := by
  obtain ⟨p,q,hpq,rfl⟩ := Finset.card_eq_two.mp hP
  have hstar := (intersecting_ten_design D hu hf hi hc).2.2 p
    (hPS (by simp)) q (hPS (by simp)) hpq
  have he : (extensions D {p,q}).image (fun a => insert a {p,q}) =
      D.filter (fun T => ({p,q} : Finset α) ⊆ T) := by
    ext T
    constructor
    · intro hT
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hT
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).2.2,Finset.subset_insert _ _⟩
    · intro hT
      obtain ⟨hTD,hPT⟩ := Finset.mem_filter.mp hT
      have hdiff : (T \ {p,q}).card = 1 := by
        rw [Finset.card_sdiff_of_subset hPT,hu T hTD]
        simp [hpq]
      obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hdiff
      have ham : a ∈ T \ {p,q} := by rw [ha]; simp
      have hshape : insert a {p,q} = T := by
        have h := Finset.union_sdiff_of_subset hPT
        rw [ha] at h
        simpa [Finset.union_comm] using h
      refine Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨?_,?_,?_⟩,hshape⟩
      · exact member_subset_support hTD (Finset.mem_sdiff.mp ham).1
      · exact (Finset.mem_sdiff.mp ham).2
      · simpa [hshape] using hTD
  have hinj : Set.InjOn (fun a : α => insert a ({p,q} : Finset α))
      (↑(extensions D {p,q}) : Set α) := by
    intro a ha b hb he
    change insert a ({p,q} : Finset α) = insert b ({p,q} : Finset α) at he
    have ham : a ∈ insert b ({p,q} : Finset α) := by
      rw [← he]
      exact Finset.mem_insert_self a _
    exact (Finset.mem_insert.mp ham).resolve_right (Finset.mem_filter.mp ha).2.1
  rw [← he,Finset.card_image_of_injOn hinj] at hstar
  exact hstar

/-- Two-point sets that each carry nine of ten units of mass have a common point. -/
theorem heavy_extensions_common_point
    (K : Finset (Finset α)) (A : Finset α) (E : Finset α → Finset α) (w : α → ℕ)
    (hK : K.Nonempty) (he : ∀ P ∈ K, (E P).card = 2)
    (hs : ∀ P ∈ K, E P ⊆ A)
    (hw : ∑ a ∈ A, w a ≤ 10) (hh : ∀ P ∈ K, 9 ≤ ∑ a ∈ E P, w a) :
    ∃ a ∈ A, ∀ P ∈ K, a ∈ E P := by
  obtain ⟨P,hP⟩ := hK
  obtain ⟨a,b,hab,hshape⟩ := Finset.card_eq_two.mp (he P hP)
  have hp := hh P hP
  rw [hshape,Finset.sum_pair hab] at hp
  have point (v : α) (hv : v ∈ A) (hvw : 5 ≤ w v) : ∀ Q ∈ K, v ∈ E Q := by
    intro Q hQ
    by_contra hn
    have hsub : insert v (E Q) ⊆ A := Finset.insert_subset hv (hs Q hQ)
    have ht := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (show ∀ i ∈ A, i ∉ insert v (E Q) → 0 ≤ w i by intros; omega)
    rw [Finset.sum_insert hn] at ht
    have hq := hh Q hQ
    omega
  have haA : a ∈ A := hs P hP (by rw [hshape]; simp)
  have hbA : b ∈ A := hs P hP (by rw [hshape]; simp)
  by_cases ha : 5 ≤ w a
  · exact ⟨a,haA,point a haA ha⟩
  · exact ⟨b,hbA,point b hbA (by omega)⟩

/-- The regular degree five of the design bounds heavy extension keys directly;
no chosen normal form or finite extension-permutation computation is required. -/
theorem heavy_design_keys_card_le_five
    (D K : Finset (Finset α)) (w : α → ℕ)
    (hu : ∀ T ∈ D, T.card = 3) (hf : IsSunflowerFree D 3)
    (hi : ∀ T ∈ D, ∀ U ∈ D, (T ∩ U).Nonempty) (hc : D.card = 10)
    (hKu : ∀ P ∈ K, P.card = 2) (hKs : ∀ P ∈ K, P ⊆ support D)
    (hw : ∑ a ∈ support D, w a ≤ 10)
    (hh : ∀ P ∈ K, 9 ≤ ∑ a ∈ extensions D P, w a) : K.card ≤ 5 := by
  by_cases hK : K.Nonempty
  · obtain ⟨a,ha,hall⟩ := heavy_extensions_common_point K (support D) (extensions D) w hK
      (fun P hP => extensions_card_two D hu hf hi hc P (hKu P hP) (hKs P hP))
      (fun P _ => Finset.filter_subset _ _) hw hh
    have him : K.image (fun P => insert a P) ⊆ D.filter (fun T => a ∈ T) := by
      intro T hT
      obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hT
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (hall P hP)).2.2,by simp⟩
    have hinj : Set.InjOn (fun P : Finset α => insert a P) (↑K : Set (Finset α)) := by
      intro P hP Q hQ he
      have hp := (Finset.mem_filter.mp (hall P hP)).2.1
      have hq := (Finset.mem_filter.mp (hall Q hQ)).2.1
      have h := congrArg (fun T : Finset α => T.erase a) he
      simpa [Finset.erase_insert,hp,hq] using h
    have hb := Finset.card_le_card him
    rw [Finset.card_image_of_injOn hinj,
      (intersecting_ten_design D hu hf hi hc).2.1 a ha] at hb
    exact hb
  · simp [Finset.not_nonempty_iff_eq_empty.mp hK]

end FrontierGenericHeavyExtensions
