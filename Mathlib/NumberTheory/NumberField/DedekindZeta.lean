/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone.NormLessThanOne
import Mathlib.NumberTheory.NumberField.Units.Regulator

variable (K : Type*) [Field K] [NumberField K]

namespace NumberField

open Filter Ideal Submodule Topology  NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.mixedEmbedding.euclidean NumberField.Units

open scoped nonZeroDivisors Real

private noncomputable def ideal.tendsto_is_principal_norm_le_div_atop_aux (s : ℝ) :
    ↑({x | x ∈ toMixed K ⁻¹' fundamentalCone K ∧ mixedEmbedding.norm ((toMixed K) x) ≤ s} ∩
        (euclidean.integerLattice K)) ≃ {a : integralPoint K | ↑(intNorm a) ≤ s} := by
  simp_rw [intNorm_coe]
  refine (((toMixed K).toEquiv.image _).trans (Equiv.setCongr ?_)).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter _ (mixedEmbedding.norm · ≤ s)).symm
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨⟨h₁, h₂⟩, ⟨x, rfl⟩⟩, rfl⟩
    refine ⟨?_, ?_⟩
    sorry
    sorry
  --  refine ⟨⟨h₁, ⟨x, ⟨x, rfl⟩, rfl⟩⟩, h₂⟩
  · rintro ⟨h, h2⟩
    refine ⟨(toMixed K).symm x, ⟨⟨?_, ?_⟩, ?_⟩ , rfl⟩
    exact h.1
    exact h2
    rw [euclidean.integerLattice_eq_symm_image]
    refine Set.mem_image_of_mem ⇑(toMixed K).symm ?_
    exact h.2

--  exact ⟨fun ⟨_, ⟨⟨h₁, h₂⟩, h₃⟩, rfl⟩ ↦ ⟨⟨h₁, h₃⟩, h₂⟩,
--    fun ⟨⟨h₁, h₂⟩, h₃⟩ ↦ ⟨(toMixed K).symm x, ⟨⟨h₁, h₃⟩, h₂⟩, rfl⟩⟩

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
  · sorry
  -- · rw [h, (volumePreserving_toMixed K).measure_preimage
  --     (measurableSet_normLessThanOne K).nullMeasurableSet, volume_normLessThanOne,
  --     euclidean.integerLattice, ZLattice.covolume_comap _ _ _ (volumePreserving_toMixed_symm K),
  --     ZLattice.covolume_eq_measure_fundamentalDomain _ _ (fundamentalDomain_integerLattice K),
  --     volume_fundamentalDomain_latticeBasis]
  --   simp_rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
  --     ENNReal.coe_toReal, NNReal.coe_real_pi, Real.coe_toNNReal _ (regulator_pos K).le,
  --     Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
  --   ring_nf
  · rwa [Set.mem_preimage, map_smul, smul_mem_iff_mem h.ne']
  · simp_rw [map_smul, mixedEmbedding.norm_smul, euclidean.finrank, abs_of_nonneg h]
  · exact (toMixed K).continuous.measurable (measurableSet_normLessThanOne K)
  · rw [h, ← ContinuousLinearEquiv.coe_toHomeomorph, ← Homeomorph.preimage_frontier,
      ContinuousLinearEquiv.coe_toHomeomorph, (volumePreserving_toMixed K).measure_preimage
      measurableSet_frontier.nullMeasurableSet, volume_frontier_normLessThanOne]

end NumberField
