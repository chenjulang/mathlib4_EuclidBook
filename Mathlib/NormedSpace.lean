import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import Mathlib.Analysis.Complex.Basic

noncomputable section

open scoped ComplexConjugate

/-- Post-composition of a continuous semilinear map by a semilinear isometry, as as a semilinear
isometry. -/
def LinearIsometry.compSL (E : Type*) {F : Type*} {G : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace ℂ E] [NormedSpace ℂ F] [NormedSpace ℂ G]
    (σ₁₂ : ℂ →+* ℂ) {σ₂₃ σ₁₃ : ℂ →+* ℂ} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
    [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃] [RingHomIsometric σ₁₂]
    (φ : F →ₛₗᵢ[σ₂₃] G) :
    (E →SL[σ₁₂] F) →ₛₗᵢ[σ₂₃] E →SL[σ₁₃] G where
  toLinearMap := (_root_.ContinuousLinearMap.compSL E F G _ _ φ.toContinuousLinearMap).toLinearMap
  norm_map' _ := φ.norm_toContinuousLinearMap_comp

/-- Flip the order of arguments of a continuous bilinear map. This is a version bundled as a
`LinearIsometryEquiv`. -/
def ContinuousLinearMap.flipₗᵢ'' (E : Type*) (F : Type*) (G : Type*)
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
    [NormedSpace ℂ E] [NormedSpace ℂ F] [NormedSpace ℂ G]
    (σ₂₃ σ₁₃ : ℂ →+* ℂ) [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃] :
    (E →SL[σ₁₃] F →SL[σ₂₃] G) ≃ₗᵢ[ℂ] F →SL[σ₂₃] E →SL[σ₁₃] G :=
  ContinuousLinearMap.flipₗᵢ' E F G σ₂₃ σ₁₃

/-- Complex conjugation, as a bijective conjugate-linear map. -/
def Complex.conjSLE : ℂ ≃ₗ⋆[ℂ] ℂ := conjAe.toRingEquiv.toSemilinearEquiv

/-- Complex conjugation, as a bijective conjugate-linear isometry. -/
def Complex.conjSLIE : ℂ ≃ₗᵢ⋆[ℂ] ℂ where
  toLinearEquiv := Complex.conjSLE
  norm_map' := Complex.abs_conj
