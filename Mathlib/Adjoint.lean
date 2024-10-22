import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.NormedSpace

noncomputable section
open scoped ComplexConjugate

#check LinearIsometry.compSL
#check ContinuousLinearMap.flipₗᵢ''
#check InnerProductSpace.toDual -- maybe make a `ℂ`-only version?
#check Complex.conjSLIE

variable {E F : Type}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
variable [CompleteSpace E] [CompleteSpace F]

#time
-- set_option trace.profiler true in
/-- The adjoint of a bounded operator from a Hilbert space `E` to a Hilbert space `F`. -/
noncomputable def ContinuousLinearMap.adjoint : (E →L[ℂ] F) →ₗᵢ⋆[ℂ] F →L[ℂ] E :=
  ((InnerProductSpace.toDual ℂ E).symm.toLinearIsometry.compSL F _).comp <|
    (ContinuousLinearMap.flipₗᵢ'' E F ℂ conj (RingHom.id ℂ)).toLinearIsometry.comp <|
    ((Complex.conjSLIE.toLinearIsometry.compSL F _).comp
      (InnerProductSpace.toDual ℂ F).toLinearIsometry).compSL E _

#time
noncomputable example : (E →L[ℂ] F) →ₗᵢ⋆[ℂ] F →L[ℂ] E :=
  LinearIsometry.comp (E₂ := F →L⋆[ℂ] NormedSpace.Dual ℂ E) (σ₁₂ := RingHom.id _) (σ₂₃ := conj)
    sorry <|
  LinearIsometry.comp (E₂ := E →L[ℂ] F →L⋆[ℂ] ℂ) (σ₁₂ := RingHom.id _) (σ₂₃ := RingHom.id _)
    sorry
    sorry
