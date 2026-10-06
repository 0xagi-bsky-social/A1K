import SunflowerLean.Erdos20TripleWitness
import Mathlib.Data.Fintype.Card

/-! Intersecting-block substitution. Each point of an outer member is replaced
by an independently selected inner member on a tagged disjoint support. -/
namespace Erdos20Substitution

open Erdos20LocalStructure Erdos20TripleWitness Erdos20StrictCore

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def Choice (F : Finset (Finset α)) (G : Finset (Finset β)) :=
  (S : F) × (S.val → G)

noncomputable instance choiceFintype (F : Finset (Finset α))
    (G : Finset (Finset β)) : Fintype (Choice F G) := by
  unfold Choice
  infer_instance

noncomputable def encode {F : Finset (Finset α)} {G : Finset (Finset β)}
    (c : Choice F G) : Finset (α × β) :=
  c.1.val.attach.biUnion (fun a => (c.2 a).val.image (fun b => (a.val, b)))

noncomputable def substitution (F : Finset (Finset α)) (G : Finset (Finset β)) :
    Finset (Finset (α × β)) := by
  classical
  exact Finset.univ.image (encode (F := F) (G := G))

theorem mem_encode {F : Finset (Finset α)} {G : Finset (Finset β)}
    (c : Choice F G) (a : α) (b : β) :
    (a, b) ∈ encode c ↔ ∃ ha : a ∈ c.1.val, b ∈ (c.2 ⟨a, ha⟩).val := by
  simp only [encode, Finset.mem_biUnion, Finset.mem_attach, true_and, Finset.mem_image]
  constructor
  · rintro ⟨⟨a', ha'⟩, b', hb', heq⟩
    have h₁ := congrArg Prod.fst heq
    have h₂ := congrArg Prod.snd heq
    simp only at h₁ h₂
    subst a'
    subst b'
    exact ⟨ha', hb'⟩
  · rintro ⟨ha, hb⟩
    exact ⟨⟨a, ha⟩, b, hb, rfl⟩

noncomputable def fiber (H : Finset (α × β)) (a : α) : Finset β :=
  (H.filter (fun z => z.1 = a)).image Prod.snd

theorem mem_fiber (H : Finset (α × β)) (a : α) (b : β) :
    b ∈ fiber H a ↔ (a, b) ∈ H := by
  simp only [fiber, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨a', b'⟩, ⟨hmem, ha⟩, hb⟩
    simp only at ha hb
    subst a'
    subst b'
    exact hmem
  · intro h
    exact ⟨(a,b), ⟨h,rfl⟩, rfl⟩

theorem fiber_encode {F : Finset (Finset α)} {G : Finset (Finset β)}
    (c : Choice F G) (a : c.1.val) :
    fiber (encode c) a.val = (c.2 a).val := by
  ext b
  simp only [mem_fiber, mem_encode]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨a.property, h⟩⟩

theorem support_encode {F : Finset (Finset α)} {G : Finset (Finset β)}
    (c : Choice F G) (hne : ∀ B ∈ G, B.Nonempty) :
    (encode c).image Prod.fst = c.1.val := by
  ext a
  constructor
  · intro h
    obtain ⟨⟨a',b⟩, hmem, heq⟩ := Finset.mem_image.mp h
    simp only at heq
    subst a'
    exact ((mem_encode c a b).mp hmem).choose
  · intro h
    obtain ⟨b, hb⟩ := hne _ (c.2 ⟨a,h⟩).property
    exact Finset.mem_image.mpr ⟨(a,b), (mem_encode c a b).mpr ⟨h,hb⟩, rfl⟩

theorem encode_injective {F : Finset (Finset α)} {G : Finset (Finset β)}
    (hne : ∀ B ∈ G, B.Nonempty) :
    Function.Injective (encode (F := F) (G := G)) := by
  intro c d heq
  have hS : c.1 = d.1 := by
    apply Subtype.ext
    rw [← support_encode c hne, ← support_encode d hne, heq]
  cases c with
  | mk S f =>
    cases d with
    | mk T g =>
      dsimp at hS
      subst T
      congr 1
      funext a
      apply Subtype.ext
      have h := congrArg (fun H => fiber H a.val) heq
      simpa only [fiber_encode] using h

theorem card_encode {F : Finset (Finset α)} {G : Finset (Finset β)}
    (c : Choice F G) (s : ℕ) (hG : ∀ B ∈ G, B.card = s) :
    (encode c).card = c.1.val.card * s := by
  classical
  rw [encode, Finset.card_biUnion]
  · have heach : ∀ a ∈ c.1.val.attach,
        ((c.2 a).val.image (fun b => (a.val,b))).card = s := by
      intro a _
      rw [Finset.card_image_of_injective]
      · exact hG _ (c.2 a).property
      · intro b b' h
        exact congrArg Prod.snd h
    rw [Finset.sum_congr rfl heach]
    simp
  · intro a _ a' _ hne
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨b, _, h⟩ := Finset.mem_image.mp hz
    obtain ⟨b', _, h'⟩ := Finset.mem_image.mp hz'
    apply hne
    apply Subtype.ext
    exact congrArg Prod.fst (h.trans h'.symm)

theorem card_substitution (F : Finset (Finset α)) (G : Finset (Finset β))
    (r : ℕ) (hF : ∀ S ∈ F, S.card = r)
    (hne : ∀ B ∈ G, B.Nonempty) :
    (substitution F G).card = F.card * G.card ^ r := by
  classical
  rw [substitution, Finset.card_image_of_injective _ (encode_injective hne)]
  change Fintype.card (Choice F G) = _
  simp only [Choice, Fintype.card_sigma, Fintype.card_fun, Fintype.card_coe]
  have h : ∀ S : F, G.card ^ S.val.card = G.card ^ r := fun S => by
    rw [hF _ S.property]
  simp_rw [h]
  simp

theorem uniform_substitution (F : Finset (Finset α)) (G : Finset (Finset β))
    (r s : ℕ) (hF : ∀ S ∈ F, S.card = r) (hG : ∀ B ∈ G, B.card = s) :
    ∀ H ∈ substitution F G, H.card = r * s := by
  intro H hH
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hH
  rw [card_encode c s hG, hF _ c.1.property]

/-- In a uniform three-sunflower-free family, equal pair intersections force
all three (possibly repeated) members to coincide. -/
theorem three_rigidity (F : Finset (Finset α)) (r : ℕ)
    (hu : ∀ S ∈ F, S.card = r) (hf : IsSunflowerFree F 3)
    {A B C : Finset α} (hA : A ∈ F) (hB : B ∈ F) (hC : C ∈ F)
    (h₁ : A ∩ B = A ∩ C) (h₂ : A ∩ B = B ∩ C) :
    A = B ∧ A = C := by
  by_cases hAB : A = B
  · subst B
    have hsub : A ⊆ C := Finset.inter_eq_left.mp (by simpa using h₁.symm)
    exact ⟨rfl, Finset.eq_of_subset_of_card_le hsub (by rw [hu C hC, hu A hA])⟩
  by_cases hAC : A = C
  · subst C
    have hsub : A ⊆ B := Finset.inter_eq_left.mp (by simpa using h₁)
    exact False.elim (hAB (Finset.eq_of_subset_of_card_le hsub
      (by rw [hu B hB, hu A hA])))
  by_cases hBC : B = C
  · subst C
    have hsub : B ⊆ A := Finset.inter_eq_right.mp (by simpa using h₂)
    exact False.elim (hAB (Finset.eq_of_subset_of_card_le hsub
      (by rw [hu A hA, hu B hB])).symm)
  exfalso
  apply hf {A,B,C} (by
    intro S hS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl <;> assumption)
  refine ⟨by simp [hAB,hAC,hBC], A ∩ B, ?_⟩
  intro S T hS hT hne
  simp only [Finset.mem_insert, Finset.mem_singleton] at hS hT
  rcases hS with rfl | rfl | rfl <;> rcases hT with rfl | rfl | rfl
  all_goals simp_all only [Finset.inter_comm, not_true_eq_false, Ne, not_false_eq_true]

theorem support_inter_encode {F : Finset (Finset α)} {G : Finset (Finset β)}
    (c d : Choice F G)
    (hint : ∀ B ∈ G, ∀ C ∈ G, (B ∩ C).Nonempty) :
    (encode c ∩ encode d).image Prod.fst = c.1.val ∩ d.1.val := by
  ext a
  constructor
  · intro h
    obtain ⟨⟨a',b⟩, hmem, heq⟩ := Finset.mem_image.mp h
    simp only at heq
    subst a'
    exact Finset.mem_inter.mpr
      ⟨((mem_encode c a b).mp (Finset.mem_inter.mp hmem).1).choose,
       ((mem_encode d a b).mp (Finset.mem_inter.mp hmem).2).choose⟩
  · intro h
    obtain ⟨hc,hd⟩ := Finset.mem_inter.mp h
    obtain ⟨b,hb⟩ := hint _ (c.2 ⟨a,hc⟩).property _ (d.2 ⟨a,hd⟩).property
    obtain ⟨hbc,hbd⟩ := Finset.mem_inter.mp hb
    exact Finset.mem_image.mpr ⟨(a,b), Finset.mem_inter.mpr
      ⟨(mem_encode c a b).mpr ⟨hc,hbc⟩,
       (mem_encode d a b).mpr ⟨hd,hbd⟩⟩, rfl⟩

theorem fiber_inter (H K : Finset (α × β)) (a : α) :
    fiber (H ∩ K) a = fiber H a ∩ fiber K a := by
  ext b
  simp only [mem_fiber, Finset.mem_inter]

/-- The substituted family is three-sunflower-free. Intersecting inner
blocks prevent a projected intersection from disappearing. -/
theorem sunflowerFree_substitution
    (F : Finset (Finset α)) (G : Finset (Finset β)) (r s : ℕ)
    (huF : ∀ A ∈ F, A.card = r) (huG : ∀ B ∈ G, B.card = s)
    (hfF : IsSunflowerFree F 3) (hfG : IsSunflowerFree G 3)
    (hint : ∀ B ∈ G, ∀ C ∈ G, (B ∩ C).Nonempty) :
    IsSunflowerFree (substitution F G) 3 := by
  classical
  intro H hsub hsun
  obtain ⟨A,B,C,hAB,hAC,hBC,hH⟩ := Finset.card_eq_three.mp hsun.1
  have hA : A ∈ H := by simp [hH]
  have hB : B ∈ H := by simp [hH]
  have hC : C ∈ H := by simp [hH]
  obtain ⟨a,_,ha⟩ := Finset.mem_image.mp (hsub hA)
  obtain ⟨b,_,hb⟩ := Finset.mem_image.mp (hsub hB)
  obtain ⟨c,_,hc⟩ := Finset.mem_image.mp (hsub hC)
  obtain ⟨core,hcore⟩ := hsun.2
  have hi₁ : encode a ∩ encode b = encode a ∩ encode c := by
    rw [ha,hb,hc,hcore A B hA hB hAB,hcore A C hA hC hAC]
  have hi₂ : encode a ∩ encode b = encode b ∩ encode c := by
    rw [ha,hb,hc,hcore A B hA hB hAB,hcore B C hB hC hBC]
  have hs₁ := congrArg (fun K => K.image Prod.fst) hi₁
  have hs₂ := congrArg (fun K => K.image Prod.fst) hi₂
  simp only [support_inter_encode _ _ hint] at hs₁ hs₂
  obtain ⟨hab,hac⟩ := three_rigidity F r huF hfF
    a.1.property b.1.property c.1.property hs₁ hs₂
  have heq : encode a = encode b := by
    ext ⟨x,y⟩
    by_cases hx : x ∈ a.1.val
    · have hxb : x ∈ b.1.val := hab ▸ hx
      have hxc : x ∈ c.1.val := hac ▸ hx
      have hf₁ := congrArg (fun K => fiber K x) hi₁
      have hf₂ := congrArg (fun K => fiber K x) hi₂
      simp only [fiber_inter] at hf₁ hf₂
      rw [fiber_encode a ⟨x,hx⟩, fiber_encode b ⟨x,hxb⟩,
        fiber_encode c ⟨x,hxc⟩] at hf₁ hf₂
      have hrig := three_rigidity G s huG hfG
        (a.2 ⟨x,hx⟩).property (b.2 ⟨x,hxb⟩).property (c.2 ⟨x,hxc⟩).property hf₁ hf₂
      rw [← mem_fiber, ← mem_fiber,
        fiber_encode a ⟨x,hx⟩, fiber_encode b ⟨x,hxb⟩, hrig.1]
    · have hxb : x ∉ b.1.val := by simpa [← hab] using hx
      simp only [mem_encode]
      constructor
      · rintro ⟨h,_⟩
        exact (hx h).elim
      · rintro ⟨h,_⟩
        exact (hxb h).elim
  exact hAB (ha.symm.trans (heq.trans hb))

theorem tenTriples_nonempty : ∀ B ∈ tenTriples, B.Nonempty := by
  intro B hB
  apply Finset.card_pos.mp
  rw [tenTriples_uniform B hB]
  decide

noncomputable def twentyThousand : Finset (Finset (Fin 12 × Fin 6)) :=
  substitution twentyTriples tenTriples

theorem twentyThousand_card : twentyThousand.card = 20000 := by
  rw [twentyThousand, card_substitution _ _ 3 twentyTriples_uniform tenTriples_nonempty,
    twentyTriples_card, tenTriples_card]
  norm_num

theorem twentyThousand_uniform : ∀ S ∈ twentyThousand, S.card = 9 :=
  uniform_substitution _ _ 3 3 twentyTriples_uniform tenTriples_uniform

theorem twentyThousand_sunflower_free : IsSunflowerFree twentyThousand 3 :=
  sunflowerFree_substitution _ _ 3 3 twentyTriples_uniform tenTriples_uniform
    twentyTriples_sunflower_free tenTriples_sunflower_free tenTriples_intersecting

theorem twenty_thousand_witness : UniformFreeWitness.{0} 3 9 20000 :=
  ⟨Fin 12 × Fin 6, inferInstance, twentyThousand, twentyThousand_uniform,
    twentyThousand_sunflower_free, twentyThousand_card⟩

/-- A concrete finite obstruction excludes exponential base three. -/
theorem not_uniformBound_three_three : ¬ UniformSunflowerBound.{0} 3 3 := by
  intro h
  have hb := h twentyThousand 9 twentyThousand_uniform twentyThousand_sunflower_free
  rw [twentyThousand_card] at hb
  norm_num at hb

/-- Every natural-number base for the three-petal conjecture must be at least four. -/
theorem uniformBound_base_ge_four {q : ℕ} (h : UniformSunflowerBound.{0} q 3) :
    4 ≤ q := by
  have hb := h twentyThousand 9 twentyThousand_uniform twentyThousand_sunflower_free
  rw [twentyThousand_card] at hb
  by_contra hn
  have hq : q ≤ 3 := by omega
  have hp : q ^ 9 ≤ 3 ^ 9 := Nat.pow_le_pow_left hq 9
  norm_num at hp
  omega

end Erdos20Substitution
