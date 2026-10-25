import SupportBound

namespace FrontierDegreeEnvelope
universe u

/-- Select two maximal values successively, retaining a bound on the entire tail. -/
theorem exists_top_two {α : Type u} [DecidableEq α]
    (s : Finset α) (w : α → ℕ) (hc : 2 ≤ s.card) :
    ∃ x y, x ∈ s ∧ y ∈ s ∧ x ≠ y ∧ w y ≤ w x ∧
      ∀ v ∈ s, v ≠ x → w v ≤ w y := by
  classical
  obtain ⟨x,hx,hmx⟩ := s.exists_max_image w (Finset.card_pos.mp (by omega))
  have hce := Finset.card_erase_add_one hx
  obtain ⟨y,hy,hmy⟩ := (s.erase x).exists_max_image w
    (Finset.card_pos.mp (by omega))
  have hyS := Finset.mem_of_mem_erase hy
  have hyx := Finset.ne_of_mem_erase hy
  refine ⟨x,y,hx,hyS,hyx.symm,hmx y hyS,?_⟩
  intro v hv hvx
  exact hmy v (Finset.mem_erase.mpr ⟨hvx,hv⟩)

/-- Select three maximal values successively. The third value bounds everything
outside the first two selected points. -/
theorem exists_top_three {α : Type u} [DecidableEq α]
    (s : Finset α) (w : α → ℕ) (hc : 3 ≤ s.card) :
    ∃ x y z, x ∈ s ∧ y ∈ s ∧ z ∈ s ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      w z ≤ w y ∧ w y ≤ w x ∧
      ∀ v ∈ s, v ≠ x → v ≠ y → w v ≤ w z := by
  classical
  obtain ⟨x,hx,hmx⟩ := s.exists_max_image w (Finset.card_pos.mp (by omega))
  have hce := Finset.card_erase_add_one hx
  obtain ⟨y,z,hy,hz,hyz,hzy,htail⟩ := exists_top_two (s.erase x) w (by omega)
  have hyS := Finset.mem_of_mem_erase hy
  have hzS := Finset.mem_of_mem_erase hz
  refine ⟨x,y,z,hx,hyS,hzS,(Finset.ne_of_mem_erase hy).symm,
    (Finset.ne_of_mem_erase hz).symm,hyz,hzy,hmx y hyS,?_⟩
  intro v hv hvx hvy
  exact htail v (Finset.mem_erase.mpr ⟨hvx,hv⟩) hvy

/-- Select four maximal values, preserving distinctness and a common tail bound. -/
theorem exists_top_four {α : Type u} [DecidableEq α]
    (s : Finset α) (w : α → ℕ) (hc : 4 ≤ s.card) :
    ∃ x y z t, x ∈ s ∧ y ∈ s ∧ z ∈ s ∧ t ∈ s ∧
      x ≠ y ∧ x ≠ z ∧ x ≠ t ∧ y ≠ z ∧ y ≠ t ∧ z ≠ t ∧
      w t ≤ w z ∧ w z ≤ w y ∧ w y ≤ w x ∧
      ∀ v ∈ s, v ≠ x → v ≠ y → v ≠ z → w v ≤ w t := by
  classical
  obtain ⟨x,hx,hmx⟩ := s.exists_max_image w (Finset.card_pos.mp (by omega))
  have hce := Finset.card_erase_add_one hx
  obtain ⟨y,z,t,hy,hz,ht,hyz,hyt,hzt,htz,hzy,htail⟩ :=
    exists_top_three (s.erase x) w (by omega)
  have hyS := Finset.mem_of_mem_erase hy
  have hzS := Finset.mem_of_mem_erase hz
  have htS := Finset.mem_of_mem_erase ht
  refine ⟨x,y,z,t,hx,hyS,hzS,htS,(Finset.ne_of_mem_erase hy).symm,
    (Finset.ne_of_mem_erase hz).symm,(Finset.ne_of_mem_erase ht).symm,
    hyz,hyt,hzt,htz,hzy,hmx y hyS,?_⟩
  intro v hv hvx hvy hvz
  exact htail v (Finset.mem_erase.mpr ⟨hvx,hv⟩) hvy hvz

/-- A degree-square envelope with an explicit exceptional set. All subtraction
is in the integers, including the excess total above one per support point. -/
theorem degree_envelope {α : Type u} [DecidableEq α]
    (s E : Finset α) (w : α → ℕ) (D : ℤ)
    (hE : E ⊆ s) (hpos : ∀ v ∈ s, 1 ≤ w v)
    (htail : ∀ v ∈ s, v ∉ E → (w v : ℤ) ≤ D) :
    (∑ v ∈ s, (w v : ℤ)*((w v : ℤ)-1)) ≤
      D * ((∑ v ∈ s, (w v : ℤ)) - (s.card : ℤ)) +
      ∑ v ∈ E, ((w v : ℤ)-D)*((w v : ℤ)-1) := by
  classical
  have hp (v : α) (hv : v ∈ s) :
      (w v : ℤ)*((w v : ℤ)-1) ≤
      D*((w v : ℤ)-1) +
        if v ∈ E then ((w v : ℤ)-D)*((w v : ℤ)-1) else 0 := by
    by_cases he : v ∈ E
    · simp only [he, if_true]
      nlinarith
    · simp only [he, if_false, add_zero]
      have hpv : (1 : ℤ) ≤ w v := by exact_mod_cast hpos v hv
      have ht := htail v hv he
      nlinarith
  have hsum := Finset.sum_le_sum hp
  have hfilter : s.filter (fun v => v ∈ E) = E := by
    ext v
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hv => ⟨hE hv,hv⟩⟩
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, hfilter] at hsum
  simpa only [← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, mul_one] using hsum

/-- Top-three degree envelope. -/
theorem envelope_three {α : Type u} [DecidableEq α]
    (s : Finset α) (w : α → ℕ) (x y z : α)
    (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
    (hpos : ∀ v ∈ s, 1 ≤ w v)
    (htail : ∀ v ∈ s, v ≠ x → v ≠ y → w v ≤ w z) :
    (∑ v ∈ s, (w v : ℤ)*((w v : ℤ)-1)) ≤
      (w z : ℤ) * ((∑ v ∈ s, (w v : ℤ)) - (s.card : ℤ)) +
      ((w x : ℤ)-(w z : ℤ))*((w x : ℤ)-1) +
      ((w y : ℤ)-(w z : ℤ))*((w y : ℤ)-1) := by
  have hh := degree_envelope s {x,y} w (w z)
    (by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl <;> assumption) hpos
    (by intro v hv hve
        have hvx : v ≠ x := by intro he; subst v; simp at hve
        have hvy : v ≠ y := by intro he; subst v; simp at hve
        exact_mod_cast htail v hv hvx hvy)
  simpa [hxy, add_assoc] using hh

/-- Top-four degree envelope. -/
theorem envelope_four {α : Type u} [DecidableEq α]
    (s : Finset α) (w : α → ℕ) (x y z t : α)
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ s)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hpos : ∀ v ∈ s, 1 ≤ w v)
    (htail : ∀ v ∈ s, v ≠ x → v ≠ y → v ≠ z → w v ≤ w t) :
    (∑ v ∈ s, (w v : ℤ)*((w v : ℤ)-1)) ≤
      (w t : ℤ) * ((∑ v ∈ s, (w v : ℤ)) - (s.card : ℤ)) +
      ((w x : ℤ)-(w t : ℤ))*((w x : ℤ)-1) +
      ((w y : ℤ)-(w t : ℤ))*((w y : ℤ)-1) +
      ((w z : ℤ)-(w t : ℤ))*((w z : ℤ)-1) := by
  have hh := degree_envelope s {x,y,z} w (w t)
    (by intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl <;> assumption) hpos
    (by intro v hv hve
        have hvx : v ≠ x := by intro he; subst v; simp at hve
        have hvy : v ≠ y := by intro he; subst v; simp at hve
        have hvz : v ≠ z := by intro he; subst v; simp at hve
        exact_mod_cast htail v hv hvx hvy hvz)
  simpa [hxy,hxz,hyz,add_assoc] using hh

/-- Convert the falling second moment to the square moment without truncated
natural-number subtraction. -/
theorem sum_falling_eq_square_sub {α : Type u} [DecidableEq α]
    (s : Finset α) (w : α → ℕ) :
    (∑ v ∈ s, (w v : ℤ)*((w v : ℤ)-1)) =
      (∑ v ∈ s, (w v : ℤ)^2) - ∑ v ∈ s, (w v : ℤ) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  ring

open Erdos20BCWConditional Erdos20DegreeCongruences

/-- Every point of the actual family support has positive degree. -/
theorem support_degree_pos {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (v : α) (hv : v ∈ support F) :
    1 ≤ degree F v := by
  obtain ⟨S,hS,hvS⟩ := Finset.mem_biUnion.mp hv
  exact Finset.card_pos.mpr ⟨S, Finset.mem_filter.mpr ⟨hS,hvS⟩⟩

/-- The degree sum over actual support equals rank times family cardinality. -/
theorem support_degree_sum {α : Type u} [DecidableEq α]
    (F : Finset (Finset α)) (r : ℕ) (hu : ∀ S ∈ F, S.card = r) :
    (∑ v ∈ support F, (degree F v : ℤ)) = (r : ℤ) * F.card := by
  have hh := FrontierSupport.weighted_incidence_sum F (fun _ => 1)
  have hsum : (∑ S ∈ F, ∑ _v ∈ S, (1 : ℕ)) = r*F.card := by
    calc
      _ = ∑ _S ∈ F, r := Finset.sum_congr rfl (fun S hS => by simp [hu S hS])
      _ = _ := by simp [Nat.mul_comm]
  simp only [mul_one] at hh
  rw [hsum] at hh
  exact_mod_cast hh.symm

end FrontierDegreeEnvelope
#print axioms FrontierDegreeEnvelope.exists_top_three
#print axioms FrontierDegreeEnvelope.exists_top_four
#print axioms FrontierDegreeEnvelope.degree_envelope
#print axioms FrontierDegreeEnvelope.envelope_three
#print axioms FrontierDegreeEnvelope.envelope_four

#print axioms FrontierDegreeEnvelope.sum_falling_eq_square_sub
#print axioms FrontierDegreeEnvelope.support_degree_pos
#print axioms FrontierDegreeEnvelope.support_degree_sum
