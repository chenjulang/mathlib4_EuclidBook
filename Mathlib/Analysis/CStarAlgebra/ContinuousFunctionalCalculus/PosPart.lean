import Mathlib

section quasispectrum

/-- The existing version should be generalized to this. -/
lemma Unitization.quasispectrum_eq_spectrum_inr'' (R : Type*) {A : Type*} [CommRing R]
    [NonUnitalRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] (a : A) :
    quasispectrum R a = spectrum R (a : Unitization R A) := by
  ext r
  have : { r | ¬ IsUnit r} ⊆ spectrum R _ := mem_spectrum_inr_of_not_isUnit a
  rw [← Set.union_eq_left.mpr this, ← quasispectrum_eq_spectrum_union]
  apply forall_congr' fun hr ↦ ?_
  rw [not_iff_not, Units.smul_def, Units.smul_def, ← inr_smul, ← inr_neg, isQuasiregular_inr_iff]

lemma NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum {R A : Type*}
    {p : outParam (A → Prop)}
    [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R] [TopologicalSemiring R]
    [ContinuousStar R] [NonUnitalRing A] [StarRing A] [TopologicalSpace A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [NonUnitalContinuousFunctionalCalculus R p]
    (a : A) : IsCompact (quasispectrum R a) :=
  isCompact_iff_compactSpace.mpr inferInstance

end quasispectrum

section stone_weierstrass

variable {𝕜 : Type*} [RCLike 𝕜]

open ContinuousMapZero NonUnitalStarAlgebra

/-- An induction principle for `C(s, 𝕜)₀`. -/
@[elab_as_elim]
lemma ContinuousMapZero.induction_on' {s : Set 𝕜} [Zero s] (h0 : ((0 : s) : 𝕜) = 0)
    {p : C(s, 𝕜)₀ → Prop} (zero : p 0) (id : p (.id h0)) (star_id : p (star (.id h0)))
    (add : ∀ f g, p f → p g → p (f + g)) (mul : ∀ f g, p f → p g → p (f * g))
    (smul : ∀ (r : 𝕜) f, p f → p (r • f))
    (closure : (∀ f ∈ adjoin 𝕜 {(.id h0 : C(s, 𝕜)₀)}, p f) → ∀ f, p f) (f : C(s, 𝕜)₀) :
    p f := by
  refine closure (fun f hf => ?_) f
  induction hf using NonUnitalAlgebra.adjoin_induction with
  | mem f hf =>
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_star] at hf
    rw [star_eq_iff_star_eq, eq_comm (b := f)] at hf
    obtain (rfl | rfl) := hf
    all_goals assumption
  | zero => exact zero
  | add _ _ _ _ hf hg => exact add _ _ hf hg
  | mul _ _ _ _ hf hg => exact mul _ _ hf hg
  | smul _ _ _ hf => exact smul _ _ hf

open Topology in
@[elab_as_elim]
theorem ContinuousMapZero.induction_on_of_compact' {s : Set 𝕜} [Zero s] (h0 : ((0 : s) : 𝕜) = 0)
    [CompactSpace s] {p : C(s, 𝕜)₀ → Prop} (zero : p 0) (id : p (.id h0))
    (star_id : p (star (.id h0))) (add : ∀ f g, p f → p g → p (f + g))
    (mul : ∀ f g, p f → p g → p (f * g)) (smul : ∀ (r : 𝕜) f, p f → p (r • f))
    (frequently : ∀ f, (∃ᶠ g in 𝓝 f, p g) → p f) (f : C(s, 𝕜)₀) :
    p f := by
  refine f.induction_on' h0 zero id star_id add mul smul fun h f ↦ frequently f ?_
  have := (ContinuousMapZero.adjoin_id_dense h0).closure_eq ▸ Set.mem_univ (x := f)
  exact mem_closure_iff_frequently.mp this |>.mp <| .of_forall h

end stone_weierstrass

section cfc_commute

lemma cfc_commute_cfc {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A] [Ring A] [StarRing A]
    [Algebra R A] [ContinuousFunctionalCalculus R p] (f g : R → R) (a : A) :
    Commute (cfc f a) (cfc g a) := by
  refine cfc_cases (fun x ↦ Commute x (cfc g a)) a f (by simp) fun hf ha ↦ ?_
  refine cfc_cases (fun x ↦ Commute _ x) a g (by simp) fun hg _ ↦ ?_
  exact Commute.all _ _ |>.map _

lemma cfcₙ_commute_cfcₙ {R A : Type*} {p : A → Prop} [CommSemiring R] [Nontrivial R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [NonUnitalContinuousFunctionalCalculus R p] (f g : R → R) (a : A) :
    Commute (cfcₙ f a) (cfcₙ g a) := by
  refine cfcₙ_cases (fun x ↦ Commute x (cfcₙ g a)) a f (by simp) fun hf hf0 ha ↦ ?_
  refine cfcₙ_cases (fun x ↦ Commute _ x) a g (by simp) fun hg hg0 _ ↦ ?_
  exact Commute.all _ _ |>.map _

end cfc_commute

section superset

local notation "σₙ" => quasispectrum
open ContinuousMapZero

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [Nontrivial R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [instCFCₙ : NonUnitalContinuousFunctionalCalculus R p]

/-- The composition of `cfcₙHom` with the natural embedding `C(s, R)₀ → C(quasispectrum R a, R)₀`
whenever `quasispectrum R a ⊆ s`.

This is sometimes necessary in order to consider the same continuous functions applied to multiple
distinct elements, with the added constraint that `cfcₙ` does not suffice. This can occur, for
example, if it is necessary to use uniqueness of this continuous functional calculus. A practical
example can be found in the proof of `CFC.posPart_negPart_unique`. -/
@[simps!]
noncomputable def cfcₙHom_superset {a : A} (ha : p a) {s : Set R} (hs : σₙ R a ⊆ s) :
    letI : Zero s := ⟨0, hs (quasispectrum.zero_mem R a)⟩
    C(s, R)₀ →⋆ₙₐ[R] A :=
  letI : Zero s := ⟨0, hs (quasispectrum.zero_mem R a)⟩
  cfcₙHom ha (R := R) |>.comp <| ContinuousMapZero.nonUnitalStarAlgHom_precomp R <|
    ⟨⟨_, continuous_id.subtype_map hs⟩, rfl⟩

lemma cfcₙHom_superset_continuous {a : A} (ha : p a) {s : Set R} (hs : σₙ R a ⊆ s) :
    Continuous (cfcₙHom_superset ha hs) :=
  letI : Zero s := ⟨0, hs (quasispectrum.zero_mem R a)⟩
  (cfcₙHom_continuous ha).comp <| ContinuousMapZero.continuous_comp_left _

lemma cfcₙHom_superset_id {a : A} (ha : p a) {s : Set R} (hs : σₙ R a ⊆ s) :
    letI : Zero s := ⟨0, hs (quasispectrum.zero_mem R a)⟩
    cfcₙHom_superset ha hs ⟨.restrict s <| .id R, rfl⟩ = a :=
  cfcₙHom_id ha

/-- this version uses `ContinuousMapZero.id`. -/
lemma cfcₙHom_superset_id' {a : A} (ha : p a) {s : Set R} (hs : σₙ R a ⊆ s) :
    letI : Zero s := ⟨0, hs (quasispectrum.zero_mem R a)⟩
    cfcₙHom_superset ha hs (.id rfl) = a :=
  cfcₙHom_id ha

lemma ContinuousMapZero.nonUnitalStarAlgHom_apply_mul_eq_zero {𝕜 A : Type*}
    [RCLike 𝕜] [NonUnitalRing A] [StarRing A] [TopologicalSpace A] [TopologicalSemiring A]
    [T2Space A] [Module 𝕜 A] [IsScalarTower 𝕜 A A] {s : Set 𝕜} [Zero s] [CompactSpace s]
    (h0 : (0 : s) = (0 : 𝕜)) (φ : C(s, 𝕜)₀ →⋆ₙₐ[𝕜] A) (a : A) (hmul_id : φ (.id h0) * a = 0)
    (hmul_star_id : φ (star (.id h0)) * a = 0) (hφ : Continuous φ) (f : C(s, 𝕜)₀) :
    φ f * a = 0 := by
  induction f using ContinuousMapZero.induction_on_of_compact' h0 with
  | zero => simp [map_zero]
  | id => exact hmul_id
  | star_id => exact hmul_star_id
  | add _ _ h₁ h₂ => simp only [map_add, add_mul, h₁, h₂, zero_add]
  | mul _ _ _ h => simp only [map_mul, mul_assoc, h, mul_zero]
  | smul _ _ h => rw [map_smul, smul_mul_assoc, h, smul_zero]
  | frequently f h => exact h.mem_of_closed <| isClosed_eq (by fun_prop) continuous_zero

lemma ContinuousMapZero.mul_nonUnitalStarAlgHom_apply_eq_zero {𝕜 A : Type*}
    [RCLike 𝕜] [NonUnitalRing A] [StarRing A] [TopologicalSpace A] [TopologicalSemiring A]
    [T2Space A] [Module 𝕜 A] [SMulCommClass 𝕜 A A] {s : Set 𝕜} [Zero s] [CompactSpace s]
    (h0 : (0 : s) = (0 : 𝕜)) (φ : C(s, 𝕜)₀ →⋆ₙₐ[𝕜] A) (a : A) (hmul_id : a * φ (.id h0) = 0)
    (hmul_star_id : a * φ (star (.id h0)) = 0) (hφ : Continuous φ) (f : C(s, 𝕜)₀) :
    a * φ f = 0 := by
  induction f using ContinuousMapZero.induction_on_of_compact' h0 with
  | zero => simp [map_zero]
  | id => exact hmul_id
  | star_id => exact hmul_star_id
  | add _ _ h₁ h₂ => simp only [map_add, mul_add, h₁, h₂, zero_add]
  | mul _ _ h _ => simp only [map_mul, ← mul_assoc, h, zero_mul]
  | smul _ _ h => rw [map_smul, mul_smul_comm, h, smul_zero]
  | frequently f h => exact h.mem_of_closed <| isClosed_eq (by fun_prop) continuous_zero

end superset


universe u

variable {A : Type u} [NonUnitalRing A] [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
variable [StarRing A] [TopologicalSpace A]
variable [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]

namespace CStarAlgebra

noncomputable instance : PosPart A where
  posPart := cfcₙ (·⁺ : ℝ → ℝ)

noncomputable instance : NegPart A where
  negPart := cfcₙ (·⁻ : ℝ → ℝ)

end CStarAlgebra

attribute [fun_prop] continuous_posPart continuous_negPart

namespace CFC

lemma posPart_def (a : A) : a⁺ = cfcₙ (·⁺ : ℝ → ℝ) a := rfl

lemma negPart_def (a : A) : a⁻ = cfcₙ (·⁻ : ℝ → ℝ) a := rfl

@[simp]
lemma posPart_mul_negPart (a : A) : a⁺ * a⁻ = 0 := by
  rw [posPart_def, negPart_def]
  by_cases ha : IsSelfAdjoint a
  · rw [← cfcₙ_mul _ _, ← cfcₙ_zero ℝ a]
    refine cfcₙ_congr (fun x _ ↦ ?_)
    simp only [_root_.posPart_def, _root_.negPart_def]
    simpa using le_total x 0
  · simp [cfcₙ_apply_of_not_predicate a ha]


@[simp]
lemma negPart_mul_posPart (a : A) : a⁻ * a⁺ = 0 :=
  posPart_mul_negPart a ▸ cfcₙ_commute_cfcₙ _ _ a

lemma posPart_sub_negPart (a : A) (ha : IsSelfAdjoint a := by cfc_tac) : a⁺ - a⁻ = a := by
  rw [posPart_def, negPart_def]
  rw [← cfcₙ_sub _ _]
  conv_rhs => rw [← cfcₙ_id ℝ a]
  congr! 2 with
  exact _root_.posPart_sub_negPart _

section Unique

variable [UniqueNonUnitalContinuousFunctionalCalculus ℝ A]

@[simp]
lemma posPart_neg (a : A) : (-a)⁺ = a⁻ := by
  by_cases ha : IsSelfAdjoint a
  · rw [posPart_def, negPart_def, ← cfcₙ_comp_neg _ _]
    congr! 2
  · have ha' : ¬ IsSelfAdjoint (-a) := fun h ↦ ha (by simpa using h.neg)
    rw [posPart_def, negPart_def, cfcₙ_apply_of_not_predicate a ha,
      cfcₙ_apply_of_not_predicate _ ha']

@[simp]
lemma negPart_neg (a : A) : (-a)⁻ = a⁺ := by
  rw [← eq_comm, ← sub_eq_zero, ← posPart_neg, neg_neg, sub_self]

end Unique

variable [PartialOrder A] [StarOrderedRing A]
    -- I absolutely hate this hypothesis, I think we need a `ContinuousSqrt` class.
    -- Then we could avoid this idiocy.
    [∀ (α : Type) [Zero α] [TopologicalSpace α], StarOrderedRing (ContinuousMapZero α ℝ)]

lemma posPart_nonneg (a : A) :
    0 ≤ a⁺ :=
  cfcₙ_nonneg (fun x _ ↦ by positivity)

lemma negPart_nonneg (a : A) :
    0 ≤ a⁻ :=
  cfcₙ_nonneg (fun x _ ↦ by positivity)

lemma eq_posPart_iff [NonnegSpectrumClass ℝ A] (a : A) : a = a⁺ ↔ 0 ≤ a := by
  refine ⟨fun ha ↦ ha ▸ posPart_nonneg a, fun ha ↦ ?_⟩
  conv_lhs => rw [← cfcₙ_id ℝ a]
  rw [posPart_def]
  refine cfcₙ_congr (fun x hx ↦ ?_)
  simpa [_root_.posPart_def] using quasispectrum_nonneg_of_nonneg a ha x hx

lemma negPart_eq_zero_iff [NonnegSpectrumClass ℝ A] (a : A) (ha : IsSelfAdjoint a) :
    a⁻ = 0 ↔ 0 ≤ a := by
  rw [← eq_posPart_iff]
  nth_rw 2 [← posPart_sub_negPart a]
  simp

variable [UniqueNonUnitalContinuousFunctionalCalculus ℝ A]

lemma eq_negPart_iff [NonnegSpectrumClass ℝ A] (a : A) : a = -a⁻ ↔ a ≤ 0 := by
  simpa [neg_eq_iff_eq_neg] using eq_posPart_iff (-a)

lemma posPart_eq_zero_iff [NonnegSpectrumClass ℝ A] (a : A) (ha : IsSelfAdjoint a) :
    a⁺ = 0 ↔ a ≤ 0 := by
  rw [← eq_negPart_iff]
  nth_rw 2 [← posPart_sub_negPart a]
  simp

-- there are even more here, like the norm condition
lemma nonneg_tfae [NonnegSpectrumClass ℝ A] (a : A) :
    List.TFAE
      [0 ≤ a,
      a = a⁺,
      IsSelfAdjoint a ∧ a⁻ = 0,
      IsSelfAdjoint a ∧ ∀ x ∈ quasispectrum ℝ a, 0 ≤ x,
      IsSelfAdjoint a ∧ QuasispectrumRestricts a ContinuousMap.realToNNReal] := by
  sorry

local notation "σₙ" => quasispectrum

open ContinuousMapZero

variable [NonnegSpectrumClass ℝ A]
variable [TopologicalRing A] [T2Space A]

open NonUnitalContinuousFunctionalCalculus in
/-- The positive and negative parts of a selfadjoint elements `a` are unique. That is, if
`a = b - c` is the difference of nonnegative elements whose product is zero, then these are
precisely `a⁺` and `a⁻`. -/
lemma posPart_negPart_unique {a b c : A} (habc : a = b - c) (hbc : b * c = 0)
    (hb : 0 ≤ b := by cfc_tac) (hc : 0 ≤ c := by cfc_tac) :
    b = a⁺ ∧ c = a⁻ := by
  /- The key idea is to show that `cfcₙ f a = cfcₙ f b + cfcₙ f (-c)` for all real-valued `f`
  continuous on the union of the spectra of `a`, `b`, and `-c`. Then apply this to `f = (·⁺)`.
  The equality holds because both sides consitute star homomorphisms which agree on `f = id` since
  `a = b - c`. -/
  /- `a`, `b`, `-c` are selfadjoint. -/
  have hb' : IsSelfAdjoint b := .of_nonneg hb
  have hc' : IsSelfAdjoint (-c) := .neg <| .of_nonneg hc
  have ha : IsSelfAdjoint a := habc ▸ hb'.sub <| .of_nonneg hc
  /- It suffices to show `b = a⁺` since `a⁺ - a⁻ = a = b - c` -/
  rw [and_iff_left_of_imp ?of_b_eq]
  case of_b_eq =>
    rw [← posPart_sub_negPart a] at habc
    rintro rfl
    linear_combination (norm := abel1) habc
  /- `s := σₙ ℝ a ∪ σₙ ℝ b ∪ σₙ ℝ (-c)` is compact and each of these sets are subsets of `s`.
  Moreover, `0 ∈ s`. -/
  let s := σₙ ℝ a ∪ σₙ ℝ b ∪ σₙ ℝ (-c)
  have hs : CompactSpace s := by
    refine isCompact_iff_compactSpace.mp <| (IsCompact.union ?_ ?_).union ?_
    all_goals exact isCompact_quasispectrum _
  obtain ⟨has, hbs, hcs⟩ : σₙ ℝ a ⊆ s ∧ σₙ ℝ b ⊆ s ∧ σₙ ℝ (-c) ⊆ s := by
    refine ⟨?_, ?_, ?_⟩; all_goals intro; aesop
  let _ : Zero s := ⟨0, by aesop⟩
  have s0 : (0 : s) = (0 : ℝ) := rfl
  /- The continuous functional calculi for functions `f g : C(s, ℝ)₀` applied to `b` and `(-c)`
  are orthogonal (i.e., the product is always zero). -/
  have mul₁ (f g : C(s, ℝ)₀) :
      (cfcₙHom_superset hb' hbs f) * (cfcₙHom_superset hc' hcs g) = 0 := by
    refine f.nonUnitalStarAlgHom_apply_mul_eq_zero s0 _ _ ?_ ?_
      (cfcₙHom_superset_continuous hb' hbs)
    swap; rw [star_trivial]
    all_goals
      refine g.mul_nonUnitalStarAlgHom_apply_eq_zero s0 _ _ ?_ ?_
        (cfcₙHom_superset_continuous hc' hcs)
      all_goals simp only [star_trivial, cfcₙHom_superset_id' hb' hbs, cfcₙHom_superset_id' hc' hcs,
        mul_neg, hbc, neg_zero]
  have mul₂ (f g : C(s, ℝ)₀) : (cfcₙHom_superset hc' hcs f) * (cfcₙHom_superset hb' hbs g) = 0 := by
    simpa only [star_mul, star_zero, ← map_star, star_trivial] using congr(star $(mul₁ g f))
  /- `fun f ↦ cfcₙ f b + cfcₙ f (-c)` defines a star homomorphism `ψ : C(s, ℝ)₀ →⋆ₙₐ[ℝ] A` which
  agrees with the star homomorphism `cfcₙ · a : C(s, ℝ)₀ →⋆ₙₐ[ℝ] A` since
  `cfcₙ id a = a = b - c = cfcₙ id b + cfcₙ id (-c)`. -/
  let ψ : C(s, ℝ)₀ →⋆ₙₐ[ℝ] A :=
    { (cfcₙHom_superset hb' hbs : C(s, ℝ)₀ →ₗ[ℝ] A) + (cfcₙHom_superset hc' hcs : C(s, ℝ)₀ →ₗ[ℝ] A)
        with
      toFun := cfcₙHom_superset hb' hbs + cfcₙHom_superset hc' hcs
      map_zero' := by simp [-cfcₙHom_superset_apply]
      map_mul' := fun f g ↦ by
        simp only [Pi.add_apply, map_mul, mul_add, add_mul, mul₂, add_zero, mul₁, zero_add]
      map_star' := fun f ↦ by simp [← map_star] }
  have key : (cfcₙHom_superset ha has) = ψ :=
    UniqueNonUnitalContinuousFunctionalCalculus.eq_of_continuous_of_map_id s rfl
    (cfcₙHom_superset ha has) ψ (cfcₙHom_superset_continuous ha has)
    ((cfcₙHom_superset_continuous hb' hbs).add (cfcₙHom_superset_continuous hc' hcs))
    (by simpa [ψ, -cfcₙHom_superset_apply, cfcₙHom_superset_id, sub_eq_add_neg] using habc)
  /- Applying the equality of star homomorphisms to the function `(·⁺ : ℝ → ℝ)` we find that
  `b = cfcₙ id b + cfcₙ 0 (-c) = cfcₙ (·⁺) b - cfcₙ (·⁺) (-c) = cfcₙ (·⁺) a = a⁺`, where the
  second equality follows because these functions are equal on the spectra of `b` and `-c`,
  respectively, since `0 ≤ b` and `-c ≤ 0`. -/
  letI f : C(s, ℝ)₀ := ⟨⟨(·⁺), by fun_prop⟩, by simp [s0]⟩
  replace key := congr($key f)
  simp only [cfcₙHom_superset_apply, NonUnitalStarAlgHom.coe_mk', NonUnitalAlgHom.coe_mk, ψ,
    Pi.add_apply, cfcₙHom_superset_apply, cfcₙHom_eq_cfcₙ_extend (·⁺)] at key
  calc
    b = cfcₙ (id : ℝ → ℝ) b + cfcₙ (0 : ℝ → ℝ) (-c) := by simp [cfcₙ_id ℝ b]
    _ = _ := by
      congr! 1
      all_goals
        refine cfcₙ_congr fun x hx ↦ Eq.symm ?_
        lift x to σₙ ℝ _ using hx
        simp only [Subtype.val_injective.extend_apply, comp_apply, coe_mk, ContinuousMap.coe_mk,
          Subtype.map_coe, id_eq, posPart_eq_self, f, Pi.zero_apply, posPart_eq_zero]
      · exact quasispectrum_nonneg_of_nonneg b hb x.val x.property
      · obtain ⟨x, hx⟩ := x
        simp only [← neg_nonneg]
        rw [Unitization.quasispectrum_eq_spectrum_inr'' ℝ (-c), Unitization.inr_neg,
          ← spectrum.neg_eq, Set.mem_neg, ← Unitization.quasispectrum_eq_spectrum_inr'' ℝ c]
          at hx
        exact quasispectrum_nonneg_of_nonneg c hc _ hx
    _ = _ := key.symm
    _ = a⁺ := by
      refine cfcₙ_congr fun x hx ↦ ?_
      lift x to σₙ ℝ a using hx
      simp [Subtype.val_injective.extend_apply, f]

end CFC
