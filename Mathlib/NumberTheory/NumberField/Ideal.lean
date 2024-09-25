/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLessThanOne
import Mathlib.NumberTheory.NumberField.Discriminant
import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# Docstring

-/

variable (K : Type*) [Field K] [NumberField K]

namespace NumberField

open Filter Ideal Submodule Topology NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.mixedEmbedding.euclidean NumberField.Units

open scoped nonZeroDivisors Real

private noncomputable def ideal.tendsto_is_principal_norm_le_div_atop_aux (s : ℝ) :
    ↑({x | x ∈ toMixed K ⁻¹' fundamentalCone K ∧ mixedEmbedding.norm ((toMixed K) x) ≤ s} ∩
        (euclidean.integerLattice K)) ≃ {a : integralPoint K | ↑(intNorm a) ≤ s} := by
  simp_rw [intNorm_coe, euclidean.integerLattice_eq_symm_image]
  refine (((toMixed K).toEquiv.image _).trans (Equiv.setCongr ?_)).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter _ (mixedEmbedding.norm · ≤ s)).symm
  ext x
  exact ⟨fun ⟨_, ⟨⟨h₁, h₂⟩, ⟨_, h₃, rfl⟩⟩, rfl⟩ ↦ ⟨⟨h₁, h₃⟩, h₂⟩,
    fun ⟨h₁, h₂⟩ ↦ ⟨(toMixed K).symm x, ⟨⟨h₁.1, h₂⟩, ⟨x, h₁.2, rfl⟩⟩, rfl⟩⟩

open Classical in
theorem ideal.tendsto_is_principal_norm_le_div_atop :
    Tendsto (fun s : ℝ ↦
      (Nat.card {I : (Ideal (𝓞 K))⁰ | IsPrincipal (I : Ideal (𝓞 K)) ∧
        absNorm (I : Ideal (𝓞 K)) ≤ s} : ℝ) / s) atTop
          (𝓝 ((2 ^ NrRealPlaces K * (2 * π) ^ NrComplexPlaces K * regulator K) /
            (torsionOrder K *  Real.sqrt |discr K|))) := by
  have h : ∀ s : ℝ,
      {x | x ∈ toMixed K ⁻¹' fundamentalCone K ∧ mixedEmbedding.norm (toMixed K x) ≤ s} =
        toMixed K ⁻¹' {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ s} := fun _ ↦ rfl
  convert (ZLattice.covolume.tendsto_card_le_div' (euclidean.integerLattice K)
      (F := fun x ↦ mixedEmbedding.norm (toMixed K x))
      (X := (toMixed K)⁻¹' (fundamentalCone K)) (fun a b c h ↦ ?_) (fun _ _ h ↦ ?_)
      (isBounded_normLessThanOne K) ?_ ?_).mul (tendsto_const_nhds (x := (torsionOrder K : ℝ)⁻¹))
      using 2 with n
  · rw [eq_comm, mul_inv_eq_iff_eq_mul₀ (Nat.cast_ne_zero.mpr (torsionOrder K).ne_zero),
      div_mul_eq_mul_div₀, ← Nat.cast_mul,  card_isPrincipal_norm_le, Nat.card_congr
      (ideal.tendsto_is_principal_norm_le_div_atop_aux K _)]
  · simp_rw [h, (volumePreserving_toMixed K).measure_preimage
      (measurableSet_normLessThanOne K).nullMeasurableSet, volume_normLessThanOne,
      euclidean.integerLattice, ZLattice.covolume_comap _ _ _ (volumePreserving_toMixed K),
      covolume_integerLattice, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
      ENNReal.coe_toReal, NNReal.coe_real_pi, Real.coe_toNNReal _ (regulator_pos K).le]
    ring_nf
  · rwa [Set.mem_preimage, map_smul, smul_mem_iff_mem h.ne']
  · simp_rw [map_smul, mixedEmbedding.norm_smul, euclidean.finrank, abs_of_nonneg h]
  · exact (toMixed K).continuous.measurable (measurableSet_normLessThanOne K)
  · rw [h, ← ContinuousLinearEquiv.coe_toHomeomorph, ← Homeomorph.preimage_frontier,
      ContinuousLinearEquiv.coe_toHomeomorph, (volumePreserving_toMixed K).measure_preimage
      measurableSet_frontier.nullMeasurableSet, volume_frontier_normLessThanOne]

end NumberField
