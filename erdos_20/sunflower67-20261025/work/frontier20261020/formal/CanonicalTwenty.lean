import SunflowerLean.Erdos20ExtremalTwenty
import SunflowerLean.Erdos20DesignNormalForm
import SunflowerLean.Erdos20V11HighSupport

namespace FrontierCanonicalTwenty
open Erdos20BCWConditional Erdos20StrictCore Erdos20DegreeCongruences
open Erdos20ExtremalTwenty Erdos20DesignNormalForm Erdos20V8Boundary

/-- The single fixed six-point design, transported by an injective map. -/
def mappedTen {α : Type*} [DecidableEq α] (e : Fin 6 ↪ α) : Finset (Finset α) :=
  (canonicalTen (0 : Fin 6) 1 2 3 4 5).image (fun S => S.image e)

/-- A direct bridge from every extremal twenty-triple family to the two fixed
canonical designs. No labelled normal-form representative is assumed as input. -/
theorem twenty_two_canonical_designs
    {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hu : ∀ P ∈ L, P.card = 3) (hf : IsSunflowerFree L 3) (hc : L.card = 20) :
    ∃ e f : Fin 6 ↪ α,
      L = mappedTen e ∪ mappedTen f ∧
      Disjoint (support (mappedTen e)) (support (mappedTen f)) := by
  obtain ⟨H,K,hL,hdis,hdesign⟩ := extremal_twenty_two_disjoint_designs L hu hf hc
  have hHsub : H ⊆ L := by rw [hL]; exact Finset.subset_union_left
  have hKsub : K ⊆ L := by rw [hL]; exact Finset.subset_union_right
  have hH := hdesign H (by simp)
  have hK := hdesign K (by simp)
  obtain ⟨e,he⟩ := ten_isomorphic_canonical H
    (fun P hP => hu P (hHsub hP))
    (fun G hG hsun => hf G (hG.trans hHsub) hsun) hH.2.1 hH.1
  obtain ⟨f,hf'⟩ := ten_isomorphic_canonical K
    (fun P hP => hu P (hKsub hP))
    (fun G hG hsun => hf G (hG.trans hKsub) hsun) hK.2.1 hK.1
  change H = mappedTen e at he
  change K = mappedTen f at hf'
  exact ⟨e,f,by simpa only [he,hf'] using hL,by simpa only [he,hf'] using hdis⟩

/-- Every degree-twenty point in an actual rank-four sunflower-free family
has a residual link consisting of two disjoint copies of the fixed design. -/
theorem high_link_two_canonical_designs
    {α : Type*} [DecidableEq α] (F : Finset (Finset α))
    (hu : ∀ R ∈ F, R.card = 4) (hf : IsSunflowerFree F 3)
    (x : α) (hx : x ∈ highPoints F) :
    ∃ e f : Fin 6 ↪ α,
      residualLink F {x} = mappedTen e ∪ mappedTen f ∧
      Disjoint (support (mappedTen e)) (support (mappedTen f)) := by
  apply twenty_two_canonical_designs
  · simpa using residualLink_uniform (core := ({x} : Finset α)) hu
  · exact residualLink_sunflowerFree hf
  · exact (Erdos20V11HighSupport.high_link_twenty_and_support_twelve F hu hf x hx).1

end FrontierCanonicalTwenty
