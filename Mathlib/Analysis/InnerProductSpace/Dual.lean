/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.Normed.Module.Dual

/-!
# The Fréchet-Riesz representation theorem

We consider an inner product space `E` over `ℂ`. We define
`toDualMap`, a conjugate-linear isometric embedding of `E` into its dual, which maps an element
`x` of the space to `fun y => ⟪x, y⟫`.

Under the hypothesis of completeness (i.e., for Hilbert spaces), we upgrade this to `toDual`, a
conjugate-linear isometric *equivalence* of `E` onto its dual; that is, we establish the
surjectivity of `toDualMap`.  This is the Fréchet-Riesz representation theorem: every element of
the dual of a Hilbert space `E` has the form `fun u => ⟪x, u⟫` for some `x : E`.

For a bounded sesquilinear form `B : E →L⋆[ℂ] E →L[ℂ] ℂ`,
we define a map `InnerProductSpace.continuousLinearMapOfBilin B : E →L[ℂ] E`,
given by substituting `E →L[ℂ] ℂ` with `E` using `toDual`.


## References

* [M. Einsiedler and T. Ward, *Functional Analysis, Spectral Theory, and Applications*]
  [EinsiedlerWard2017]

## Tags

dual, Fréchet-Riesz
-/


noncomputable section

open scoped Classical
open ComplexConjugate

universe u v

namespace InnerProductSpace

open RCLike ContinuousLinearMap

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]

local notation "⟪" x ", " y "⟫" => @inner ℂ E _ x y

local postfix:90 "†" => starRingEnd _

/-- An element `x` of an inner product space `E` induces an element of the dual space `Dual ℂ E`,
the map `fun y => ⟪x, y⟫`; moreover this operation is a conjugate-linear isometric embedding of `E`
into `Dual ℂ E`.
If `E` is complete, this operation is surjective, hence a conjugate-linear isometric equivalence;
see `toDual`.
-/
def toDualMap : E →ₗᵢ⋆[ℂ] NormedSpace.Dual ℂ E :=
  { innerSL ℂ with norm_map' := innerSL_apply_norm _ }

variable {E}

@[simp]
theorem toDualMap_apply {x y : E} : toDualMap E x y = ⟪x, y⟫ :=
  rfl

theorem innerSL_norm [Nontrivial E] : ‖(innerSL ℂ : E →L⋆[ℂ] E →L[ℂ] ℂ)‖ = 1 :=
  show ‖(toDualMap E).toContinuousLinearMap‖ = 1 from LinearIsometry.norm_toContinuousLinearMap _

theorem ext_inner_left_basis {ι : Type*} {x y : E} (b : Basis ι ℂ E)
    (h : ∀ i : ι, ⟪b i, x⟫ = ⟪b i, y⟫) : x = y := by
  apply (toDualMap E).map_eq_iff.mp
  refine (Function.Injective.eq_iff ContinuousLinearMap.coe_injective).mp (Basis.ext b ?_)
  intro i
  simp only [ContinuousLinearMap.coe_coe]
  rw [toDualMap_apply, toDualMap_apply]
  rw [← inner_conj_symm]
  conv_rhs => rw [← inner_conj_symm]
  exact congr_arg conj (h i)

theorem ext_inner_right_basis {ι : Type*} {x y : E} (b : Basis ι ℂ E)
    (h : ∀ i : ι, ⟪x, b i⟫ = ⟪y, b i⟫) : x = y := by
  refine ext_inner_left_basis b fun i => ?_
  rw [← inner_conj_symm]
  conv_rhs => rw [← inner_conj_symm]
  exact congr_arg conj (h i)

variable (E)
variable [CompleteSpace E]

/-- Fréchet-Riesz representation: any `ℓ` in the dual of a Hilbert space `E` is of the form
`fun u => ⟪y, u⟫` for some `y : E`, i.e. `toDualMap` is surjective.
-/
def toDual : E ≃ₗᵢ⋆[ℂ] NormedSpace.Dual ℂ E :=
  LinearIsometryEquiv.ofSurjective (toDualMap E)
    (by
      intro ℓ
      set Y := LinearMap.ker ℓ
      by_cases htriv : Y = ⊤
      · have hℓ : ℓ = 0 := by
          have h' := LinearMap.ker_eq_top.mp htriv
          rw [← coe_zero] at h'
          apply coe_injective
          exact h'
        exact ⟨0, by simp [hℓ]⟩
      · rw [← Submodule.orthogonal_eq_bot_iff] at htriv
        change Yᗮ ≠ ⊥ at htriv
        rw [Submodule.ne_bot_iff] at htriv
        obtain ⟨z : E, hz : z ∈ Yᗮ, z_ne_0 : z ≠ 0⟩ := htriv
        refine ⟨(starRingEnd (R := ℂ) (ℓ z) / ⟪z, z⟫) • z, ?_⟩
        apply ContinuousLinearMap.ext
        intro x
        have h₁ : ℓ z • x - ℓ x • z ∈ Y := by
          rw [LinearMap.mem_ker, map_sub, ContinuousLinearMap.map_smul,
            ContinuousLinearMap.map_smul, Algebra.id.smul_eq_mul, Algebra.id.smul_eq_mul, mul_comm]
          exact sub_self (ℓ x * ℓ z)
        have h₂ : ℓ z * ⟪z, x⟫ = ℓ x * ⟪z, z⟫ :=
          haveI h₃ :=
            calc
              0 = ⟪z, ℓ z • x - ℓ x • z⟫ := by
                rw [(Y.mem_orthogonal' z).mp hz]
                exact h₁
              _ = ⟪z, ℓ z • x⟫ - ⟪z, ℓ x • z⟫ := by rw [inner_sub_right]
              _ = ℓ z * ⟪z, x⟫ - ℓ x * ⟪z, z⟫ := by simp [inner_smul_right]
          sub_eq_zero.mp (Eq.symm h₃)
        have h₄ :=
          calc
            ⟪(ℓ z† / ⟪z, z⟫) • z, x⟫ = ℓ z / ⟪z, z⟫ * ⟪z, x⟫ := by simp [inner_smul_left, conj_conj]
            _ = ℓ z * ⟪z, x⟫ / ⟪z, z⟫ := by rw [← div_mul_eq_mul_div]
            _ = ℓ x * ⟪z, z⟫ / ⟪z, z⟫ := by rw [h₂]
            _ = ℓ x := by field_simp [inner_self_ne_zero.2 z_ne_0]
        exact h₄)

variable {E}

@[simp]
theorem toDual_apply {x y : E} : toDual E x y = ⟪x, y⟫ :=
  rfl

@[simp]
theorem toDual_symm_apply {x : E} {y : NormedSpace.Dual ℂ E} : ⟪(toDual E).symm y, x⟫ = y x := by
  rw [← toDual_apply]
  simp only [LinearIsometryEquiv.apply_symm_apply]

/-- Maps a bounded sesquilinear form to its continuous linear map,
given by interpreting the form as a map `B : E →L⋆[ℂ] NormedSpace.Dual ℂ E`
and dualizing the result using `toDual`.
-/
def continuousLinearMapOfBilin (B : E →L⋆[ℂ] E →L[ℂ] ℂ) : E →L[ℂ] E :=
  comp (toDual E).symm.toContinuousLinearEquiv.toContinuousLinearMap B

local postfix:1024 "♯" => continuousLinearMapOfBilin

variable (B : E →L⋆[ℂ] E →L[ℂ] ℂ)

@[simp]
theorem continuousLinearMapOfBilin_apply (v w : E) : ⟪B♯ v, w⟫ = B v w := by
  rw [continuousLinearMapOfBilin, coe_comp', ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, Function.comp_apply, toDual_symm_apply]

theorem unique_continuousLinearMapOfBilin {v f : E} (is_lax_milgram : ∀ w, ⟪f, w⟫ = B v w) :
    f = B♯ v := by
  refine ext_inner_right ℂ ?_
  intro w
  rw [continuousLinearMapOfBilin_apply]
  exact is_lax_milgram w

end InnerProductSpace
