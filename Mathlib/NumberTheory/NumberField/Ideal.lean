/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLessThanOne
import Mathlib.NumberTheory.NumberField.Discriminant
import Mathlib.NumberTheory.NumberField.ClassNumber
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
        (euclidean.integerLattice K)) ≃
        {a : integralPoint K | mixedEmbedding.norm (a : mixedSpace K) ≤ s} := by
  sorry
  -- simp_rw [intNorm_coe, euclidean.integerLattice_eq_symm_image]
  -- refine (((toMixed K).toEquiv.image _).trans (Equiv.setCongr ?_)).trans
  --   (Equiv.subtypeSubtypeEquivSubtypeInter _ (mixedEmbedding.norm · ≤ s)).symm
  -- ext x
  -- exact ⟨fun ⟨_, ⟨⟨h₁, h₂⟩, ⟨_, h₃, rfl⟩⟩, rfl⟩ ↦ ⟨⟨h₁, h₃⟩, h₂⟩,
  --   fun ⟨h₁, h₂⟩ ↦ ⟨(toMixed K).symm x, ⟨⟨h₁.1, h₂⟩, ⟨x, h₁.2, rfl⟩⟩, rfl⟩⟩

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
      (X := (toMixed K)⁻¹' (fundamentalCone K)) (fun _ _ _ h ↦ ?_) (fun _ _ h ↦ ?_)
      (isBounded_normLessThanOne K) ?_ ?_).mul (tendsto_const_nhds (x := (torsionOrder K : ℝ)⁻¹))
      using 2
  · rw [eq_comm, mul_inv_eq_iff_eq_mul₀ (Nat.cast_ne_zero.mpr (torsionOrder K).ne_zero),
      div_mul_eq_mul_div₀, ← Nat.cast_mul, card_isPrincipal_norm_le, Nat.card_congr
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

open Classical in
private noncomputable def ideal.tendsto_mk_eq_norm_le_div_atop_aux₁ (J : (Ideal (𝓞 K))⁰) (s : ℝ) :
    ↑({x | x ∈ (toMixed K) ⁻¹' fundamentalCone K ∧ mixedEmbedding.norm ((toMixed K) x) ≤ s} ∩
      (ZLattice.comap ℝ (idealLattice K ((FractionalIdeal.mk0 K) J)) (toMixed K).toLinearMap))
        ≃ {a : idealPoint K J | mixedEmbedding.norm (a : mixedSpace K) ≤ s} := by
  sorry

private theorem ideal.tendsto_mk_eq_norm_le_div_atop_aux₂ (C : ClassGroup (𝓞 K))
    (J : (Ideal (𝓞 K))⁰) (hJ : ClassGroup.mk0 J = C⁻¹) (s : ℝ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ | ClassGroup.mk0 I = C ∧ absNorm (I : Ideal (𝓞 K)) ≤ s}
      = Nat.card {I : (Ideal (𝓞 K))⁰ | (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
        absNorm (I : Ideal (𝓞 K)) ≤ s * absNorm (J : Ideal (𝓞 K))} := by
  let e : {I : (Ideal (𝓞 K))⁰ | ClassGroup.mk0 I = C} ≃
      {I : (Ideal (𝓞 K))⁰ | (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K))} := by
    refine Set.BijOn.equiv ?_ ⟨?_, ?_, ?_⟩
    · intro I
      exact I * J
    · intro I hI
      refine ⟨Dvd.intro_left _ rfl, ?_⟩
      refine (ClassGroup.mk0_eq_one_iff ?_).mp ?_
      · sorry
      · rw [Submonoid.coe_mul]
        rw [← @Submonoid.mul_def]
        rw [_root_.map_mul, hJ, hI, mul_inv_cancel]
    · sorry
    · sorry
  let f := Equiv.subtypeEquiv e (p := fun I ↦ absNorm (I.val : Ideal (𝓞 K)) ≤ s)
    (q := fun I ↦ absNorm (I.val : Ideal (𝓞 K)) ≤ s * (absNorm (J : Ideal (𝓞 K)) : ℝ)) ?_
  · have := Nat.card_congr f
    simp at this
    sorry
  intro I
  simp [e, Set.BijOn.equiv]
  rw [_root_.mul_le_mul_right]
  rw [Nat.cast_pos]
  refine Nat.zero_lt_of_ne_zero ?_
  exact absNorm_ne_zero_of_nonZeroDivisors J

theorem ideal.tendsto_mk_eq_norm_le_div_atop (C : ClassGroup (𝓞 K)) :
    Tendsto (fun s : ℝ ↦
      (Nat.card {I : (Ideal (𝓞 K))⁰ | ClassGroup.mk0 I = C ∧
        absNorm (I : Ideal (𝓞 K)) ≤ s} : ℝ) / s) atTop
          (𝓝 ((2 ^ NrRealPlaces K * (2 * π) ^ NrComplexPlaces K * regulator K) /
            (torsionOrder K *  Real.sqrt |discr K|))) := by
  classical
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C⁻¹
  have t1 : Tendsto (fun s : ℝ ↦ s * absNorm (J : Ideal (𝓞 K))) atTop atTop := sorry
  have t2 := (ZLattice.covolume.tendsto_card_le_div'
      (ZLattice.comap ℝ (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J))
        (toMixed K).toLinearMap)
      (F := fun x ↦ mixedEmbedding.norm (toMixed K x))
      (X := (toMixed K)⁻¹' (fundamentalCone K)) (fun _ _ _ h ↦ ?_) (fun _ _ h ↦ ?_)
      (isBounded_normLessThanOne K) ?_ ?_).mul (tendsto_const_nhds
        (x := (absNorm (J : Ideal (𝓞 K)) : ℝ) * (torsionOrder K : ℝ)⁻¹))
  have := Filter.Tendsto.comp t2 t1
  clear t1 t2
  · convert this using 2
    · rw [Function.comp_def]
      sorry
    · sorry
#exit

  classical
  have h : ∀ s : ℝ,
      {x | x ∈ toMixed K ⁻¹' fundamentalCone K ∧ mixedEmbedding.norm (toMixed K x) ≤ s} =
        toMixed K ⁻¹' {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ s} := fun _ ↦ rfl

  convert (ZLattice.covolume.tendsto_card_le_div'
      (ZLattice.comap ℝ (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J))
        (toMixed K).toLinearMap)
      (F := fun x ↦ mixedEmbedding.norm (toMixed K x))
      (X := (toMixed K)⁻¹' (fundamentalCone K)) (fun _ _ _ h ↦ ?_) (fun _ _ h ↦ ?_)
      (isBounded_normLessThanOne K) ?_ ?_).mul (tendsto_const_nhds
        (x := (absNorm (J : Ideal (𝓞 K)) : ℝ) * (torsionOrder K : ℝ)⁻¹)) using 2 with s
  · have := ideal.tendsto_mk_eq_norm_le_div_atop_aux₁ K J s
    have := Nat.card_congr this
    rw [this]
    rw [← card_isPrincipal_div_norm_le]
    rw [ideal.tendsto_mk_eq_norm_le_div_atop_aux₂ K C J hJ]
    rw [Nat.cast_mul]
    ring_nf
    rw [mul_inv_cancel_right₀]
    exact Nat.cast_ne_zero.mpr (torsionOrder K).ne_zero
  · simp_rw [h, (volumePreserving_toMixed K).measure_preimage
      (measurableSet_normLessThanOne K).nullMeasurableSet, volume_normLessThanOne,
      ZLattice.covolume_comap _ _ _ (volumePreserving_toMixed K), covolume_idealLattice,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.coe_toReal,
      NNReal.coe_real_pi, Real.coe_toNNReal _ (regulator_pos K).le]
    simp_rw [FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]
    ring_nf
    rw [mul_inv_cancel_right₀]
    rw [Nat.cast_ne_zero]
    exact absNorm_ne_zero_of_nonZeroDivisors J
  · rwa [Set.mem_preimage, map_smul, smul_mem_iff_mem h.ne']
  · simp_rw [map_smul, mixedEmbedding.norm_smul, euclidean.finrank, abs_of_nonneg h]
  · exact (toMixed K).continuous.measurable (measurableSet_normLessThanOne K)
  · rw [h, ← ContinuousLinearEquiv.coe_toHomeomorph, ← Homeomorph.preimage_frontier,
      ContinuousLinearEquiv.coe_toHomeomorph, (volumePreserving_toMixed K).measure_preimage
      measurableSet_frontier.nullMeasurableSet, volume_frontier_normLessThanOne]

open Classical in
theorem ideal.tendsto_is_principal_norm_le_div_atop' :
    Tendsto (fun s : ℝ ↦
      (Nat.card {I : (Ideal (𝓞 K))⁰ | IsPrincipal (I : Ideal (𝓞 K)) ∧
        absNorm (I : Ideal (𝓞 K)) ≤ s} : ℝ) / s) atTop
          (𝓝 ((2 ^ NrRealPlaces K * (2 * π) ^ NrComplexPlaces K * regulator K) /
            (torsionOrder K *  Real.sqrt |discr K|))) := by
  sorry

theorem ideal.tendsto_norm_le_div_atop :
    Tendsto (fun s : ℝ ↦
      (Nat.card {I : (Ideal (𝓞 K))⁰ | absNorm (I : Ideal (𝓞 K)) ≤ s} : ℝ) / s) atTop
          (𝓝 ((2 ^ NrRealPlaces K * (2 * π) ^ NrComplexPlaces K * regulator K * classNumber K) /
            (torsionOrder K *  Real.sqrt |discr K|))) := by
  classical
  convert tendsto_finset_sum Finset.univ (fun C _  ↦ ideal.tendsto_mk_eq_norm_le_div_atop K C)
    with s
  · have : {I : (Ideal (𝓞 K))⁰ | absNorm (I : Ideal (𝓞 K)) ≤ s}.Finite := by
      sorry
    rw [Nat.card_eq_card_finite_toFinset this, Finset.card_eq_sum_card_fiberwise
      (f := fun I ↦ ClassGroup.mk0 I) (t := Finset.univ), Nat.cast_sum, Finset.sum_div]
    congr! with C
    have : {I : (Ideal (𝓞 K))⁰ | ClassGroup.mk0 I = C ∧ absNorm (I : Ideal (𝓞 K)) ≤ s}.Finite :=
      sorry
    rw [Nat.card_eq_card_finite_toFinset this]
    congr
    ext
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, and_comm]
    intro _ _
    exact Finset.mem_univ _
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, classNumber]
    ring


end NumberField
