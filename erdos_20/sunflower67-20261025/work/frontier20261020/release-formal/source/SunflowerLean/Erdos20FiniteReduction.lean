import SunflowerLean.Erdos20Critical

/-!
# A finite obstruction domain for each proposed sunflower bound

Every fixed-rank counterexample can be truncated and relabelled onto an explicit
finite ordinal. The resulting bounded search is equivalent to the universal
fixed-rank statement, but no claim of practical search complexity is made.
-/
namespace Erdos20FiniteReduction

open Erdos20BCWConditional Erdos20StrictCore Erdos20Critical

universe u v

/-- Apply an embedding to every member of a finite set family. -/
def mapFamily {α : Type u} {β : Type v} (e : α ↪ β)
    (family : Finset (Finset α)) : Finset (Finset β) :=
  family.map (Finset.mapEmbedding e).toEmbedding

@[simp] theorem card_mapFamily {α : Type u} {β : Type v}
    (e : α ↪ β) (family : Finset (Finset α)) :
    (mapFamily e family).card = family.card := Finset.card_map _

/-- Relabelling preserves and reflects sunflowers, including ranks/petal counts
with vacuous pairwise conditions. -/
theorem isSunflower_mapFamily_iff
    {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (family : Finset (Finset α)) (p : ℕ) :
    IsSunflower (mapFamily e family) p ↔ IsSunflower family p := by
  constructor
  · rintro ⟨hcard, core, hcore⟩
    refine ⟨by simpa using hcard, core.preimage e e.injective.injOn, ?_⟩
    intro S T hS hT hne
    have hmap := hcore (S.map e) (T.map e)
      (Finset.mem_map.mpr ⟨S, hS, rfl⟩)
      (Finset.mem_map.mpr ⟨T, hT, rfl⟩)
      (fun h => hne ((Finset.map_injective e) h))
    have hpre := congrArg (fun U : Finset β => U.preimage e e.injective.injOn) hmap
    simpa only [← Finset.map_inter, Finset.preimage_map] using hpre
  · rintro ⟨hcard, core, hcore⟩
    refine ⟨by simpa using hcard, core.map e, ?_⟩
    intro S T hS hT hne
    obtain ⟨S', hS', rfl⟩ := Finset.mem_map.mp hS
    obtain ⟨T', hT', rfl⟩ := Finset.mem_map.mp hT
    have hne' : S' ≠ T' := fun h => hne (by subst h; rfl)
    change S'.map e ∩ T'.map e = core.map e
    rw [← Finset.map_inter, hcore S' T' hS' hT' hne']

/-- Sunflower-freeness is invariant under injective relabelling. -/
theorem isSunflowerFree_mapFamily_iff
    {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (family : Finset (Finset α)) (p : ℕ) :
    IsSunflowerFree (mapFamily e family) p ↔ IsSunflowerFree family p := by
  constructor
  · intro hfree sunflower hsub hsun
    apply hfree (mapFamily e sunflower)
    · exact Finset.map_subset_map.mpr hsub
    · exact (isSunflower_mapFamily_iff e sunflower p).mpr hsun
  · intro hfree sunflower hsub hsun
    obtain ⟨original, hsub', rfl⟩ := Finset.subset_map_iff.mp hsub
    exact hfree original hsub' ((isSunflower_mapFamily_iff e original p).mp hsun)

/-- Uniform rank is preserved by an embedding. -/
theorem uniform_mapFamily
    {α : Type u} {β : Type v} (e : α ↪ β)
    (family : Finset (Finset α)) (r : ℕ)
    (huniform : ∀ S ∈ family, S.card = r) :
    ∀ T ∈ mapFamily e family, T.card = r := by
  intro T hT
  obtain ⟨S, hS, rfl⟩ := Finset.mem_map.mp hT
  change (S.map e).card = r
  simpa using huniform S hS

/-- Restrict the type of a set to a specified finite ambient support. -/
def restrictSet {α : Type u} [DecidableEq α] (ambient S : Finset α) :
    Finset ambient := ambient.attach.filter (fun x => x.val ∈ S)

/-- Forgetting the support subtype recovers every set contained in that support. -/
theorem map_restrictSet {α : Type u} [DecidableEq α]
    (ambient S : Finset α) (hsub : S ⊆ ambient) :
    (restrictSet ambient S).map (Function.Embedding.subtype _) = S := by
  ext x
  simp only [Finset.mem_map, restrictSet, Finset.mem_filter, Finset.mem_attach,
    true_and, Function.Embedding.subtype_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hsub hx⟩, hx, rfl⟩

/-- Compress a family to its finite support and then pad to any larger finite
ordinal. The original ambient type may be infinite or live in any universe. -/
theorem exists_fin_relabel
    {α : Type u} [DecidableEq α]
    (family : Finset (Finset α)) (n r p : ℕ)
    (hsupport : (support family).card ≤ n)
    (huniform : ∀ S ∈ family, S.card = r)
    (hfree : IsSunflowerFree family p) :
    ∃ compressed : Finset (Finset (Fin n)),
      compressed.card = family.card ∧
      (∀ S ∈ compressed, S.card = r) ∧ IsSunflowerFree compressed p := by
  classical
  let ambient := support family
  let restricted : Finset (Finset ambient) := family.image (restrictSet ambient)
  let forget : ambient ↪ α := Function.Embedding.subtype _
  have hrecover : mapFamily forget restricted = family := by
    unfold mapFamily restricted
    rw [Finset.map_eq_image, Finset.image_image]
    calc
      _ = family.image id := Finset.image_congr (by
        intro S hS
        exact map_restrictSet ambient S (member_subset_support hS))
      _ = family := Finset.image_id
  have hrcard : restricted.card = family.card := by
    rw [← card_mapFamily forget restricted, hrecover]
  have hruniform : ∀ S ∈ restricted, S.card = r := by
    intro S hS
    have hmem : S.map forget ∈ family := by
      rw [← hrecover]
      exact Finset.mem_map.mpr ⟨S, hS, rfl⟩
    simpa using huniform (S.map forget) hmem
  have hrfree : IsSunflowerFree restricted p :=
    (isSunflowerFree_mapFamily_iff forget restricted p).mp (by simpa [hrecover] using hfree)
  let number : ambient ≃ Fin ambient.card :=
    (Fintype.equivFin ambient).trans (finCongr (Fintype.card_coe ambient))
  let embed : ambient ↪ Fin n := number.toEmbedding.trans (Fin.castLEEmb hsupport)
  refine ⟨mapFamily embed restricted, ?_, uniform_mapFamily embed restricted r hruniform, ?_⟩
  · simpa using hrcard
  · exact (isSunflowerFree_mapFamily_iff embed restricted p).mpr hrfree

/-- Explicit finite domain large enough for every exact-size obstruction. -/
def obstructionSize (q r : ℕ) : ℕ := r * (q ^ r + 1)

/-- An exact-size obstruction living in a canonical finite type. -/
def FiniteObstruction (q p r : ℕ) : Prop :=
  ∃ family : Finset (Finset (Fin (obstructionSize q r))),
    (∀ S ∈ family, S.card = r) ∧ IsSunflowerFree family p ∧
      family.card = q ^ r + 1

/-- Any fixed-rank counterexample, on any ambient type, has an explicit finite
ordinal representative of exactly the critical size. -/
theorem finiteObstruction_of_counterexample
    {α : Type u} [DecidableEq α]
    (family : Finset (Finset α)) (q p r : ℕ)
    (huniform : ∀ S ∈ family, S.card = r)
    (hfree : IsSunflowerFree family p)
    (hlarge : q ^ r < family.card) : FiniteObstruction q p r := by
  obtain ⟨critical, _, hcard, hcuniform, hcfree⟩ :=
    exists_exact_size_free_subfamily family r q p huniform hfree hlarge
  have hsupp : (support critical).card ≤ obstructionSize q r :=
    exact_size_support_card_bound critical r q hcuniform hcard
  obtain ⟨compressed, hccard, hcunif, hcfree'⟩ :=
    exists_fin_relabel critical (obstructionSize q r) r p hsupp hcuniform hcfree
  exact ⟨compressed, hcunif, hcfree', hccard.trans hcard⟩

/-- A canonical finite obstruction exists exactly when the proposed bound fails
at the given rank. The equivalence is independent of ambient universe. -/
theorem rankCounterexample_iff_finiteObstruction (q p r : ℕ) :
    RankCounterexample.{u} q p r ↔ FiniteObstruction q p r := by
  constructor
  · rintro ⟨α, inst, family, huniform, hfree, hlarge⟩
    exact finiteObstruction_of_counterexample family q p r huniform hfree hlarge
  · rintro ⟨family, huniform, hfree, hcard⟩
    let e : Fin (obstructionSize q r) ↪ ULift.{u} (Fin (obstructionSize q r)) :=
      Equiv.ulift.symm.toEmbedding
    refine ⟨ULift.{u} (Fin (obstructionSize q r)), inferInstance, mapFamily e family,
      uniform_mapFamily e family r huniform,
      (isSunflowerFree_mapFamily_iff e family p).mpr hfree, ?_⟩
    rw [card_mapFamily, hcard]
    omega

/-- The full fixed-base extremal bound is equivalent to absence of one explicit
finite obstruction at every rank. This is an unbounded family of finite tests. -/
theorem uniformBound_iff_no_finiteObstruction (q p : ℕ) :
    UniformSunflowerBound.{u} q p ↔ ∀ r, ¬ FiniteObstruction q p r := by
  constructor
  · intro hbound r hfinite
    obtain ⟨α, inst, family, huniform, hfree, hlarge⟩ :=
      (rankCounterexample_iff_finiteObstruction.{u} q p r).mpr hfinite
    exact (Nat.not_lt_of_ge (hbound family r huniform hfree)) hlarge
  · intro hnone α inst family r huniform hfree
    by_contra hnot
    exact hnone r (finiteObstruction_of_counterexample family q p r huniform hfree
      (Nat.lt_of_not_ge hnot))

instance finiteSunflowerDecidable (n : ℕ) (family : Finset (Finset (Fin n))) (p : ℕ) :
    Decidable (IsSunflower family p) := by
  unfold IsSunflower
  infer_instance

/-- Sunflower-freeness can be tested on p-element subfamilies alone. -/
theorem sunflowerFree_iff_powersetCard
    {α : Type u} [DecidableEq α] (family : Finset (Finset α)) (p : ℕ) :
    IsSunflowerFree family p ↔
      ∀ subfamily ∈ family.powersetCard p, ¬ IsSunflower subfamily p := by
  constructor
  · intro hfree subfamily hmem
    exact hfree subfamily (Finset.mem_powersetCard.mp hmem).1
  · intro htest subfamily hsub hsun
    exact htest subfamily (Finset.mem_powersetCard.mpr ⟨hsub, hsun.1⟩) hsun

instance finiteFreeDecidable (n : ℕ) (family : Finset (Finset (Fin n))) (p : ℕ) :
    Decidable (IsSunflowerFree family p) :=
  decidable_of_iff
    (∀ subfamily ∈ family.powersetCard p, ¬ IsSunflower subfamily p)
    (sunflowerFree_iff_powersetCard family p).symm

instance finiteObstructionDecidable (q p r : ℕ) :
    Decidable (FiniteObstruction q p r) := by
  unfold FiniteObstruction
  infer_instance

/-- A terminating but generally enormous exact decision procedure. -/
def obstructionCheck (q p r : ℕ) : Bool := decide (FiniteObstruction q p r)

/-- The Boolean checker exactly reflects fixed-rank counterexamples. -/
theorem obstructionCheck_eq_true_iff (q p r : ℕ) :
    obstructionCheck q p r = true ↔ RankCounterexample.{u} q p r := by
  rw [rankCounterexample_iff_finiteObstruction]
  simp [obstructionCheck]

/-- A negative checker result certifies the bound at that rank for every
ambient type, without assumptions on its cardinality. -/
theorem bound_of_obstructionCheck_eq_false
    {α : Type u} [DecidableEq α]
    (family : Finset (Finset α)) (q p r : ℕ)
    (hcheck : obstructionCheck q p r = false)
    (huniform : ∀ S ∈ family, S.card = r)
    (hfree : IsSunflowerFree family p) : family.card ≤ q ^ r := by
  by_contra hnot
  have hfinite := finiteObstruction_of_counterexample family q p r huniform hfree
    (Nat.lt_of_not_ge hnot)
  have htrue : obstructionCheck q p r = true := by simpa [obstructionCheck] using hfinite
  rw [hcheck] at htrue
  cases htrue

/-- The universal fixed-base bound requires successful finite checks at every
rank; a finite initial segment alone does not prove it. -/
theorem uniformBound_iff_all_checks_false (q p : ℕ) :
    UniformSunflowerBound.{u} q p ↔ ∀ r, obstructionCheck q p r = false := by
  rw [uniformBound_iff_no_finiteObstruction]
  simp [obstructionCheck]

/-- A failed bound has a least failing rank with an obstruction in the explicit
finite domain and valid universal bounds at every smaller rank. -/
theorem exists_minimal_finiteObstruction
    {q p : ℕ} (hfailure : ¬ UniformSunflowerBound.{u} q p) :
    ∃ r, 0 < r ∧ LowerRanksBound.{u} q p r ∧ FiniteObstruction q p r := by
  obtain ⟨r, hr, hlower, α, inst, family, huniform, hfree, hcard⟩ :=
    exists_minimal_critical hfailure
  refine ⟨r, hr, hlower, finiteObstruction_of_counterexample family q p r huniform hfree ?_⟩
  omega

/-- Rank zero never supplies an obstruction, including at base zero. -/
theorem obstructionCheck_rank_zero (q p : ℕ) : obstructionCheck q p 0 = false := by
  have hnone : ¬ FiniteObstruction q p 0 := by
    rintro ⟨family, huniform, _, hcard⟩
    have h := exact_size_rank_pos family 0 q huniform hcard
    omega
  simpa [obstructionCheck] using hnone

/-- A small positive control evaluated by the Lean kernel. -/
theorem obstructionCheck_positive_control : obstructionCheck 0 3 1 = true := by
  decide

/-- A small negative control evaluated by the Lean kernel. -/
theorem obstructionCheck_negative_control : obstructionCheck 1 2 1 = false := by
  decide

/-- Enumerate only uniform families with exactly the required number of members. -/
def candidateFamilies (q r : ℕ) :
    Finset (Finset (Finset (Fin (obstructionSize q r)))) :=
  ((Finset.univ : Finset (Fin (obstructionSize q r))).powersetCard r).powersetCard
    (q ^ r + 1)

/-- Candidate membership enforces exactly the rank and size requirements. -/
theorem mem_candidateFamilies_iff (q r : ℕ)
    (family : Finset (Finset (Fin (obstructionSize q r)))) :
    family ∈ candidateFamilies q r ↔
      (∀ S ∈ family, S.card = r) ∧ family.card = q ^ r + 1 := by
  simp only [candidateFamilies, Finset.mem_powersetCard, Finset.subset_iff,
    Finset.mem_univ, implies_true, true_and]

/-- Exact size of the bounded search space before sunflower-freeness is tested. -/
theorem card_candidateFamilies (q r : ℕ) :
    (candidateFamilies q r).card =
      ((obstructionSize q r).choose r).choose (q ^ r + 1) := by
  simp [candidateFamilies, Finset.card_powersetCard]

/-- Canonical obstruction existence is equivalent to a finite search over the
explicitly enumerated uniform, exact-size candidates. -/
theorem finiteObstruction_iff_candidate (q p r : ℕ) :
    FiniteObstruction q p r ↔
      ∃ family ∈ candidateFamilies q r, IsSunflowerFree family p := by
  constructor
  · rintro ⟨family, huniform, hfree, hcard⟩
    exact ⟨family, (mem_candidateFamilies_iff q r family).mpr ⟨huniform, hcard⟩, hfree⟩
  · rintro ⟨family, hcandidate, hfree⟩
    obtain ⟨huniform, hcard⟩ := (mem_candidateFamilies_iff q r family).mp hcandidate
    exact ⟨family, huniform, hfree, hcard⟩

/-- Exact finite search restricted to uniform families of critical size.
This definition is executable, but the proved search-space size is enormous. -/
def candidateCheck (q p r : ℕ) : Bool :=
  decide (((candidateFamilies q r).filter (fun family => IsSunflowerFree family p)).Nonempty)

/-- The restricted search and the general finite-obstruction decision agree. -/
theorem candidateCheck_eq_obstructionCheck (q p r : ℕ) :
    candidateCheck q p r = obstructionCheck q p r := by
  simp only [candidateCheck, obstructionCheck, Finset.filter_nonempty_iff,
    ← finiteObstruction_iff_candidate]

/-- The full extremal bound is equivalent to rejection of every candidate at
every rank. There is no claimed finite rank cutoff in this equivalence. -/
theorem uniformBound_iff_all_candidate_checks_false (q p : ℕ) :
    UniformSunflowerBound.{u} q p ↔ ∀ r, candidateCheck q p r = false := by
  simp only [candidateCheck_eq_obstructionCheck, uniformBound_iff_all_checks_false]

end Erdos20FiniteReduction
