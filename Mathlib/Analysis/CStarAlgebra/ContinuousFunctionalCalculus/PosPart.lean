--import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib

namespace StarAlgebra

@[elab_as_elim]
theorem StarAlgebra.adjoin_induction'' {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A]
    [Algebra R A] [StarRing A] [StarModule R A] {s : Set A} {p : A → Prop}
    (mem : ∀ x ∈ s, p x) (algebraMap : ∀ (r : R), p ((_root_.algebraMap R A) r)) (add : ∀ (x y : A), p x → p y → p (x + y)) (mul : ∀ (x y : A), p x → p y → p (x * y)) (star : ∀ (x : A), p x → p (Star.star x)) :

    {a : A} (h : a ∈ StarAlgebra.adjoin R s) : p a
p a

end StarAlgebra

namespace ContinuousMap

variable {𝕜 : Type*} [RCLike 𝕜]


open StarSubalgebra in
@[elab_as_elim]
lemma induction_on {s : Set 𝕜} [CompactSpace s] {P : C(s, 𝕜) → Prop}
    (algebraMap : ∀ k, P (algebraMap 𝕜 C(s, 𝕜) k)) (add : ∀ f g, P f → P g → P (f + g))
    (mul : ∀ f g, P f → P g → P (f * g)) (star : ∀ f, P f → P (star f))
    (closure : ∀ s : Set C(s, 𝕜), (∀ f ∈ s, P f) → ∀ f ∈ closure s, P f) (f : C(s, 𝕜)) :
    P f := by
  have hf : f ∈ (polynomialFunctions s).starClosure.topologicalClosure :=
    polynomialFunctions.starClosure_topologicalClosure s ▸ StarSubalgebra.mem_top
  rw [← SetLike.mem_coe, topologicalClosure_coe] at hf
  refine closure (polynomialFunctions s).starClosure (fun f hf ↦ ?_) f hf
  rw [SetLike.mem_coe, polynomialFunctions.starClosure_eq_adjoin_X] at hf





  sorry

end ContinuousMap

#exit

section superset

local notation "σₙ" => quasispectrum
open ContinuousMapZero

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [Nontrivial R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [instCFCₙ : NonUnitalContinuousFunctionalCalculus R p]

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

end superset


universe u

variable {A : Type u} [NonUnitalRing A] [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
variable [StarRing A] [TopologicalSpace A]
variable [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]

noncomputable instance : PosPart A where
  posPart := cfcₙ (·⁺ : ℝ → ℝ)

noncomputable instance : NegPart A where
  negPart := cfcₙ (·⁻ : ℝ → ℝ)

---@[to_additive (attr := fun_prop)]
---lemma continuous_oneLePart {α : Type*} [Group α] [Lattice α] [TopologicalSpace α]
    ---[ContinuousSup α] : Continuous (·⁺ᵐ : α → α) := by
  ---simp only [oneLePart_def]
  ---fun_prop

---@[to_additive (attr := fun_prop)]
---lemma continuous_leOnePart {α : Type*} [Group α] [Lattice α] [TopologicalSpace α]
    ---[ContinuousSup α] : Continuous (·⁺ᵐ : α → α) := by
  ---simp only [oneLePart_def]
  ---fun_prop

attribute [fun_prop] continuous_posPart continuous_negPart

namespace CFC

lemma posPart_def (a : A) : a⁺ = cfcₙ (·⁺ : ℝ → ℝ) a := rfl

lemma negPart_def (a : A) : a⁻ = cfcₙ (·⁻ : ℝ → ℝ) a := rfl

lemma posPart_mul_negPart (a : A) : a⁺ * a⁻ = 0 := by
  rw [posPart_def, negPart_def]
  by_cases ha : IsSelfAdjoint a
  · rw [← cfcₙ_mul _ _, ← cfcₙ_zero ℝ a]
    refine cfcₙ_congr (fun x _ ↦ ?_)
    simp only [_root_.posPart_def, _root_.negPart_def]
    simpa using le_total x 0
  · simp [cfcₙ_apply_of_not_predicate a ha]

lemma posPart_sub_negPart (a : A) (ha : IsSelfAdjoint a := by cfc_tac) : a⁺ - a⁻ = a := by
  rw [posPart_def, negPart_def]
  rw [← cfcₙ_sub _ _]
  conv_rhs => rw [← cfcₙ_id ℝ a]
  congr! 2 with
  exact _root_.posPart_sub_negPart _

section Unique

variable [UniqueNonUnitalContinuousFunctionalCalculus ℝ A]

lemma posPart_neg (a : A) : (-a)⁺ = a⁻ := by
  by_cases ha : IsSelfAdjoint a
  · rw [posPart_def, negPart_def, ← cfcₙ_comp_neg _ _]
    congr! 2
  · have ha' : ¬ IsSelfAdjoint (-a) := fun h ↦ ha (by simpa using h.neg)
    rw [posPart_def, negPart_def, cfcₙ_apply_of_not_predicate a ha,
      cfcₙ_apply_of_not_predicate _ ha']

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

variable [UniqueNonUnitalContinuousFunctionalCalculus ℝ A] [TopologicalRing A]

lemma posPart_negPart_unique {a b c : A} (habc : a = b - c) (hbc : b * c = 0)
    (ha : IsSelfAdjoint a := by cfc_tac) (hb : 0 ≤ b := by cfc_tac) (hc : 0 ≤ c := by cfc_tac) :
    b = a⁺ ∧ c = a⁻ := by
  replace ha : IsSelfAdjoint a := ha -- autoParam bug
  let s := σₙ ℝ a ∪ σₙ ℝ b ∪ σₙ ℝ (-c)
  have ha_spec := UniqueNonUnitalContinuousFunctionalCalculus.compactSpace_quasispectrum a (R := ℝ)
  have hb_spec := UniqueNonUnitalContinuousFunctionalCalculus.compactSpace_quasispectrum b (R := ℝ)
  have hc_spec := UniqueNonUnitalContinuousFunctionalCalculus.compactSpace_quasispectrum c (R := ℝ)
  have hc'_spec : CompactSpace (σₙ ℝ (-c)) := by

    sorry
  sorry
  #exit
  have hs : CompactSpace s := by
    rw [← isCompact_iff_compactSpace] at ha_spec hb_spec hc_spec ⊢
    exact (ha_spec.union hb_spec).union hc_spec
  have has : σₙ ℝ a ⊆ s := Set.subset_union_left.trans Set.subset_union_left
  have hbs : σₙ ℝ b ⊆ s := Set.subset_union_right.trans Set.subset_union_left
  have hcs : σₙ ℝ c ⊆ s := Set.subset_union_right
  have hb' : IsSelfAdjoint b := .of_nonneg hb
  have hc' : IsSelfAdjoint c := .of_nonneg hc
  let _ : Zero s := ⟨0, by aesop⟩
  have s0 : (0 : s) = (0 : ℝ) := rfl
  let ψ : C(s, ℝ)₀ →⋆ₙₐ[ℝ] A :=
    { (cfcₙHom_superset hb' hbs : C(s, ℝ)₀ →ₗ[ℝ] A) - (cfcₙHom_superset hc' hcs : C(s, ℝ)₀ →ₗ[ℝ] A) with
      toFun := cfcₙHom_superset hb' hbs - cfcₙHom_superset hc' hcs
      map_zero' := by simp [- cfcₙHom_superset_apply]
      map_mul' := fun f g ↦ by
        simp only [Pi.sub_apply, map_mul, sub_mul, mul_sub]
        -- need an induction argument to show that the cross terms are zero, gross
        sorry
      map_star' := fun f ↦ by simp [← map_star] }
  have := UniqueNonUnitalContinuousFunctionalCalculus.eq_of_continuous_of_map_id s rfl
    (cfcₙHom_superset (R := ℝ) ha has) ψ (cfcₙHom_superset_continuous ha has) ?_ ?_
    --(cfcₙHom_superset_id ha has) ?_
  · letI f : C(s, ℝ)₀ := ⟨⟨(·⁺), by fun_prop⟩, by simp [s0]⟩
    have := congr($this f)
    simp [ψ] at this

    sorry
  · exact (cfcₙHom_superset_continuous hb' hbs).sub (cfcₙHom_superset_continuous hc' hcs)
  · simpa [ψ, cfcₙHom_superset_id ha has, cfcₙHom_superset_id hb' hbs, cfcₙHom_superset_id hc' hcs]
  #exit
  let φ : C(s, ℝ)₀ →⋆ₙₐ[ℝ] A := (cfcₙHom ha (R := ℝ)).comp <|
    ContinuousMapZero.nonUnitalStarAlgHom_precomp ℝ <|
    ⟨⟨_, continuous_id.subtype_map fun x hx ↦ by aesop (add simp s)⟩, rfl⟩
  have hφ : Continuous φ := (cfcₙHom_continuous ha).comp <| ContinuousMapZero.continuous_comp_left _
  sorry



end CFC

end Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.PosPart
