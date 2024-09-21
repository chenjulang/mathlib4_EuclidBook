/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone.Basic
import Mathlib.NumberTheory.NumberField.Discriminant
import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# Fundamental Cone

In this file, we study the subset `NormLessThanOne` of the `fundamentalCone` defined as the
subset of elements `x` in the `fundamentalCone` such that `mixedEmbedding.norm x ≤ 1`.

Mainly, we want to prove that its frontier has volume zero and compute its volume. For this, we
follow in part the strategy given in [D. Marcus, *Number Fields*][marcus1977number].

## Strategy of proof

* `polarCoordMixedSpace` and `lintegral_eq_lintegral_polarCoordMixedSpace_symm`



-/

variable (K : Type*) [Field K]

open Bornology NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units

namespace NumberField.mixedEmbedding

noncomputable section realSpace

/-- DOCSTRING -/
abbrev realSpace := InfinitePlace K → ℝ

variable {K}

/-- DOCSTRING -/
def realToMixed : (realSpace K) →L[ℝ] (mixedSpace K) := ContinuousLinearMap.prod
  (ContinuousLinearMap.pi fun w ↦ ContinuousLinearMap.proj w.val)
  (ContinuousLinearMap.pi fun w ↦ Complex.ofRealCLM.comp (ContinuousLinearMap.proj w.val))

@[simp]
theorem realToMixed_apply_of_isReal (x :realSpace K) {w : InfinitePlace K}
    (hw : IsReal w) : (realToMixed x).1 ⟨w, hw⟩ = x w := rfl

@[simp]
theorem realToMixed_apply_of_isComplex (x : realSpace K) {w : InfinitePlace K}
    (hw : IsComplex w) : (realToMixed x).2 ⟨w, hw⟩ = x w := rfl

@[simp]
theorem normAtPlace_realToMixed (w : InfinitePlace K) (x : realSpace K) :
    normAtPlace w (realToMixed x) = ‖x w‖ := by
  obtain hw | hw := isReal_or_isComplex w
  · simp [normAtPlace_apply_isReal hw, realToMixed]
  · simp [normAtPlace_apply_isComplex hw, realToMixed]

@[simp]
theorem norm_realToMixed [NumberField K] (x : realSpace K) :
    mixedEmbedding.norm (realToMixed x) = ∏ w, ‖x w‖ ^ w.mult :=
  Finset.prod_congr rfl fun w _ ↦ by simp

theorem pos_norm_realToMixed [NumberField K] {x : realSpace K} (hx : ∀ w, x w ≠ 0) :
    0 < mixedEmbedding.norm (realToMixed x) := by
  rw [norm_realToMixed]
  exact Finset.prod_pos fun w _ ↦ pow_pos (abs_pos.mpr (hx w)) _

theorem logMap_realToMixed [NumberField K] {x : realSpace K}
    (hx : mixedEmbedding.norm (realToMixed x) = 1) :
    logMap (realToMixed x) = fun w ↦ (mult w.val) * Real.log (x w.val) := by
  ext
  rw [logMap_apply_of_norm_one hx, normAtPlace_realToMixed, Real.norm_eq_abs, Real.log_abs]

open Classical in
/-- DOCSTRING -/
def mixedToReal (x : mixedSpace K) : realSpace K :=
    fun w ↦ if hw : IsReal w then x.1 ⟨w, hw⟩ else ‖x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩‖

@[simp]
theorem mixedToReal_apply_of_isReal (x : mixedSpace K) (w : {w // IsReal w}) :
    mixedToReal x w.val = x.1 w := by
  rw [mixedToReal, dif_pos]

theorem mixedToReal_apply_of_isComplex (x : mixedSpace K) (w : {w // IsComplex w}) :
    mixedToReal x w.val = ‖x.2 w‖ := by
  rw [mixedToReal, dif_neg (not_isReal_iff_isComplex.mpr w.prop)]

theorem mixedToReal_smul (x : mixedSpace K) {r : ℝ} (hr : 0 ≤ r) :
    mixedToReal (r • x) = r • mixedToReal x := by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · simp_rw [Pi.smul_apply, mixedToReal_apply_of_isReal _ ⟨w, hw⟩, Prod.smul_fst, Pi.smul_apply]
  · simp_rw [Pi.smul_apply, mixedToReal_apply_of_isComplex _ ⟨w, hw⟩, Prod.smul_snd, Pi.smul_apply,
      _root_.norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, smul_eq_mul]

open Classical in
theorem realToMixedToReal (x : realSpace K) :
    mixedToReal (realToMixed x) = fun w ↦ if IsReal w then x w else ‖x w‖ := by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · rw [mixedToReal_apply_of_isReal _ ⟨w, hw⟩, realToMixed_apply_of_isReal _ hw, if_pos hw]
  · rw [mixedToReal_apply_of_isComplex _ ⟨w, hw⟩, realToMixed_apply_of_isComplex _ hw,
    if_neg (not_isReal_iff_isComplex.mpr hw), Complex.norm_real]

@[simp]
theorem realToMixedToReal_eq_self_of_nonneg {x : realSpace K} (hx : ∀ w, IsComplex w → 0 ≤ x w) :
    mixedToReal (realToMixed x) = x := by
  rw [realToMixedToReal]
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · rw [if_pos hw]
  · rw [if_neg (not_isReal_iff_isComplex.mpr hw), Real.norm_eq_abs, abs_of_nonneg (hx w hw)]

theorem mixedToRealToMixed (x : mixedSpace K) :
    realToMixed (mixedToReal x) = (fun w ↦ x.1 w, fun w ↦ (‖x.2 w‖ : ℂ)) := by
  ext w
  · rw [realToMixed_apply_of_isReal, mixedToReal_apply_of_isReal]
  · rw [realToMixed_apply_of_isComplex, mixedToReal_apply_of_isComplex]

theorem norm_mixedToReal (x : mixedSpace K) (w : InfinitePlace K) :
    ‖mixedToReal x w‖ = normAtPlace w x := by
  obtain hw | hw := isReal_or_isComplex w
  · rw [mixedToReal_apply_of_isReal _ ⟨w, hw⟩, normAtPlace_apply_isReal]
  · rw [mixedToReal_apply_of_isComplex _ ⟨w, hw⟩, normAtPlace_apply_isComplex, norm_norm]

theorem norm_mixedToRealToMixed [NumberField K] (x : mixedSpace K) :
    mixedEmbedding.norm (realToMixed (mixedToReal x)) = mixedEmbedding.norm x := by
  simp_rw [norm_realToMixed, norm_mixedToReal, mixedEmbedding.norm_apply]

@[simp]
theorem logMap_mixedToRealToMixed_of_norm_one [NumberField K] {x : mixedSpace K}
    (hx : mixedEmbedding.norm x = 1) : logMap (realToMixed (mixedToReal x)) = logMap x := by
  ext
  rw [logMap_apply_of_norm_one hx, logMap_apply_of_norm_one (by rwa [norm_mixedToRealToMixed]),
    normAtPlace_realToMixed, ← norm_mixedToReal]

open Classical in
theorem norm_realToMixed_prod_units_rpow [NumberField K] {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (u : ι → (𝓞 K)ˣ) :
    mixedEmbedding.norm (realToMixed fun w : InfinitePlace K ↦ ∏ i, w (u i) ^ c i) = 1 :=
  calc
  _ = |∏ w : InfinitePlace K, ∏ i, (w (u i) ^ c i) ^ w.mult| := by
    simp_rw [norm_realToMixed, Real.norm_eq_abs, Finset.abs_prod, abs_pow, Finset.prod_pow]
  _ = |∏ w : InfinitePlace K, ∏ i, (w (u i) ^ w.mult) ^ c i| := by
    simp_rw [← Real.rpow_natCast, ← Real.rpow_mul (apply_nonneg _ _), mul_comm]
  _ = |∏ i, (∏ w : InfinitePlace K, (w (u i) ^ w.mult)) ^ c i| := by
    rw [Finset.prod_comm]
    simp_rw [Real.finset_prod_rpow _ _ (fun _ _ ↦ pow_nonneg (apply_nonneg _ _) _)]
  _ = 1 := by
    simp_rw [prod_eq_abs_norm, Units.norm, Rat.cast_one, Real.one_rpow,
      Finset.prod_const_one, abs_one]

end realSpace

noncomputable section polarCoord

open MeasureTheory MeasureTheory.Measure MeasurableEquiv

open scoped Real

open Classical in
/-- DOCSTRING -/
def realProdComplexProdMeasurableEquiv :
    ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ × ℝ) ≃ᵐ
       (realSpace K) × ({w : InfinitePlace K // IsComplex w} → ℝ) :=
  MeasurableEquiv.trans (prodCongr (refl _)
      (arrowProdEquivProdArrow ℝ ℝ _)) <|
    MeasurableEquiv.trans prodAssoc.symm <|
       MeasurableEquiv.trans
        (prodCongr (prodCongr (refl _)
          (arrowCongr' (Equiv.subtypeEquivRight (fun _ ↦ not_isReal_iff_isComplex.symm)) (refl _)))
            (refl _))
          (prodCongr (piEquivPiSubtypeProd (fun _ ↦ ℝ) _).symm (refl _))

open Classical in
/-- DOCSTRING -/
def realProdComplexProdEquiv :
    ({w : InfinitePlace K // IsReal w} → ℝ) ×
      ({w : InfinitePlace K // IsComplex w} → ℝ × ℝ) ≃ₜ
        (realSpace K) × ({w : InfinitePlace K // IsComplex w} → ℝ) where
  __ := realProdComplexProdMeasurableEquiv K
  continuous_toFun := by
    change Continuous fun x ↦ ⟨fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else
      (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w ↦ (x.2 w).2⟩
    refine continuous_prod_mk.mpr ⟨continuous_pi_iff.mpr fun w ↦ ?_, by fun_prop⟩
    by_cases hw : IsReal w
    · simp_rw [dif_pos hw]; fun_prop
    · simp_rw [dif_neg hw]; fun_prop
  continuous_invFun := by
    change Continuous fun x ↦ (fun w ↦ x.1 w.val, fun w ↦ ⟨x.1 w.val, x.2 w⟩)
    fun_prop

open Classical in
theorem volume_preserving_realProdComplexProdEquiv [NumberField K] :
    MeasurePreserving (realProdComplexProdEquiv K) := by
  change MeasurePreserving (realProdComplexProdMeasurableEquiv K) volume volume
  exact MeasurePreserving.trans ((MeasurePreserving.id volume).prod
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ {w : InfinitePlace K // IsComplex w})) <|
    MeasurePreserving.trans (volume_preserving_prodAssoc.symm) <|
      MeasurePreserving.trans
        (((MeasurePreserving.id volume).prod (volume_preserving_arrowCongr' _
        (MeasurableEquiv.refl ℝ)
          (MeasurePreserving.id volume))).prod (MeasurePreserving.id volume))
      <| ((volume_preserving_piEquivPiSubtypeProd (fun _ : InfinitePlace K ↦ ℝ)
        (fun w : InfinitePlace K ↦ IsReal w)).symm).prod (MeasurePreserving.id volume)

open Classical in
@[simp]
theorem realProdComplexProdEquiv_apply (x : ({w : InfinitePlace K // IsReal w} → ℝ) ×
    ({w : InfinitePlace K // IsComplex w} → ℝ × ℝ)) :
    realProdComplexProdEquiv K x = ⟨fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else
      (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w ↦ (x.2 w).2⟩ := rfl

@[simp]
theorem realProdComplexProdEquiv_symm_apply (x : (realSpace K) ×
    ({w : InfinitePlace K // IsComplex w} → ℝ)) :
    (realProdComplexProdEquiv K).symm x = (fun w ↦ x.1 w.val, fun w ↦ ⟨x.1 w.val, x.2 w⟩) := rfl

variable [NumberField K]

/-- DOCSTRING -/
def polarCoordMixedSpace : PartialHomeomorph
    (mixedSpace K) ((realSpace K) × ({w : InfinitePlace K // IsComplex w} → ℝ)) :=
  ((PartialHomeomorph.refl _).prod
    (PartialHomeomorph.pi fun _ ↦ Complex.polarCoord)).transHomeomorph (realProdComplexProdEquiv K)

open Classical in
theorem polarCoordMixedSpace_target : (polarCoordMixedSpace K).target =
  (Set.univ.pi fun w ↦
      if IsReal w then Set.univ else Set.Ioi 0) ×ˢ (Set.univ.pi fun _ ↦ Set.Ioo (-π) π):= by
  rw [polarCoordMixedSpace, PartialHomeomorph.transHomeomorph_target]
  ext
  simp_rw [Set.mem_preimage, realProdComplexProdEquiv_symm_apply, PartialHomeomorph.prod_target,
    Set.mem_prod, PartialHomeomorph.refl_target, PartialHomeomorph.pi_target,
    Complex.polarCoord_target]
  aesop

theorem polarCoordMixedSpace_symm_apply (x : (realSpace K) × ({w // IsComplex w} → ℝ)) :
    (polarCoordMixedSpace K).symm x = ⟨fun w ↦ x.1 w.val,
      fun w ↦ Complex.polarCoord.symm (x.1 w, x.2 w)⟩ := rfl

theorem measurableSet_polarCoordMixedSpace_target :
    MeasurableSet (polarCoordMixedSpace K).target :=
  (polarCoordMixedSpace K).open_target.measurableSet

theorem polarCoordMixedSpace_apply (x : mixedSpace K) :
    polarCoordMixedSpace K x =
      (realProdComplexProdEquiv K) (x.1, fun w ↦ Complex.polarCoord (x.2 w)) := by
  rw [polarCoordMixedSpace]
  simp_rw [PartialHomeomorph.transHomeomorph_apply, PartialHomeomorph.prod_apply,
    PartialHomeomorph.refl_apply, id_eq, Function.comp_apply]
  rfl

theorem continuous_polarCoordMixedSpace_symm :
    Continuous (polarCoordMixedSpace K).symm := by
  change Continuous (fun x ↦ (polarCoordMixedSpace K).symm x)
  simp_rw [polarCoordMixedSpace_symm_apply]
  rw [continuous_prod_mk]
  exact ⟨by fun_prop,
    continuous_pi_iff.mpr fun i ↦ Complex.continuous_polarCoord_symm.comp' (by fun_prop)⟩

theorem realProdComplexProdEquiv_preimage_target :
  (realProdComplexProdEquiv K) ⁻¹' (polarCoordMixedSpace K).target =
    Set.univ ×ˢ Set.univ.pi fun _ ↦ polarCoord.target := by
  ext
  simp_rw [polarCoordMixedSpace_target, Set.mem_preimage, realProdComplexProdEquiv_apply,
    polarCoord_target, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies, true_and,
    Set.mem_ite_univ_left, not_isReal_iff_isComplex, Set.mem_prod]
  refine ⟨fun ⟨h₁, h₂⟩ i ↦ ⟨?_, h₂ i⟩, fun h ↦ ⟨fun i hi ↦ ?_, fun i ↦ (h i).2⟩⟩
  · specialize h₁ i i.prop
    rwa [dif_neg (not_isReal_iff_isComplex.mpr i.prop)] at h₁
  · rw [dif_neg (not_isReal_iff_isComplex.mpr hi)]
    exact (h ⟨i, hi⟩).1

open Classical in
theorem lintegral_eq_lintegral_polarCoordMixedSpace_symm (f : (mixedSpace K) → ENNReal)
    (hf : Measurable f) :
    ∫⁻ x, f x =
      ∫⁻ x in (polarCoordMixedSpace K).target,
        (∏ w : {w // IsComplex w}, (x.1 w.val).toNNReal) *
          f ((polarCoordMixedSpace K).symm x) := by
  have h : Measurable fun x ↦ (∏ w : { w // IsComplex w}, (x.1 w.val).toNNReal) *
      f ((polarCoordMixedSpace K).symm x) := by
    refine Measurable.mul ?_ ?_
    · exact measurable_coe_nnreal_ennreal_iff.mpr <| Finset.measurable_prod _ fun _ _ ↦ by fun_prop
    · exact hf.comp' (continuous_polarCoordMixedSpace_symm K).measurable
  rw [← (volume_preserving_realProdComplexProdEquiv K).setLIntegral_comp_preimage
    (measurableSet_polarCoordMixedSpace_target K) h, volume_eq_prod, volume_eq_prod,
    lintegral_prod _ hf.aemeasurable]
  simp_rw [Complex.lintegral_pi_comp_polarCoord_symm _ (hf.comp' measurable_prod_mk_left)]
  rw [realProdComplexProdEquiv_preimage_target, ← Measure.restrict_prod_eq_univ_prod,
    lintegral_prod _ (h.comp' (realProdComplexProdEquiv K).measurable).aemeasurable]
  simp_rw [realProdComplexProdEquiv_apply, polarCoordMixedSpace_symm_apply,
    dif_pos (Subtype.prop _), dif_neg (not_isReal_iff_isComplex.mpr (Subtype.prop _))]

end polarCoord

noncomputable section mapToUnitsPow

open FiniteDimensional Finset NumberField.Units.dirichletUnitTheorem

variable [NumberField K]

open Classical in
/-- DOCSTRING -/
-- This cannot be a `PartiaHomeomorph` because the target is not an open set
def mapToUnitsPow₀_aux :
    PartialEquiv ({w : InfinitePlace K // w ≠ w₀} → ℝ) (realSpace K) where
  toFun := fun c w ↦ if hw : w = w₀ then
      Real.exp (- ((w₀ : InfinitePlace K).mult : ℝ)⁻¹ * ∑ w : {w // w ≠ w₀}, c w)
    else Real.exp ((w.mult : ℝ)⁻¹ * c ⟨w, hw⟩)
  invFun := fun x w ↦ w.val.mult * Real.log (x w.val)
  source := Set.univ
  target := {x | ∀ w, 0 < x w} ∩ {x | ∑ w, w.mult * Real.log (x w) = 0}
  map_source' _ _ := by
    dsimp only
    refine ⟨Set.mem_setOf.mpr fun w ↦ by split_ifs <;> exact Real.exp_pos _, ?_⟩
    simp_rw [Set.mem_setOf_eq, ← Finset.univ.sum_erase_add _ (mem_univ w₀), dif_pos]
    rw [sum_subtype _ (by aesop : ∀ w, w ∈ univ.erase w₀ ↔ w ≠ w₀)]
    conv_lhs => enter [1,2,w]; rw [dif_neg w.prop]
    simp_rw [Real.log_exp, neg_mul, mul_neg, mul_inv_cancel_left₀ mult_coe_ne_zero,
      add_neg_eq_zero]
    infer_instance
  map_target' _ _ := trivial
  left_inv' := by
    intro x _
    dsimp only
    ext w
    rw [dif_neg w.prop, Real.log_exp, mul_inv_cancel_left₀ mult_coe_ne_zero]
  right_inv' := by
    intro x hx
    ext w
    dsimp only
    by_cases hw : w = w₀
    · rw [hw, dif_pos rfl, ← sum_subtype _
        (by aesop : ∀ w, w ∈ univ.erase w₀ ↔ w ≠ w₀) (fun w ↦ w.mult * Real.log (x w))]
      rw [sum_erase_eq_sub (mem_univ w₀), hx.2, _root_.zero_sub, neg_mul, mul_neg,
        neg_neg, inv_mul_cancel_left₀ mult_coe_ne_zero, Real.exp_log (hx.1 w₀)]
    · rw [dif_neg hw, inv_mul_cancel_left₀ mult_coe_ne_zero, Real.exp_log (hx.1 w)]

theorem mapToUnitsPow₀_aux_symm_apply (x : realSpace K) :
    (mapToUnitsPow₀_aux K).symm x = fun w ↦ w.val.mult * Real.log (x w.val) := rfl

theorem continuous_mapToUnitsPow₀_aux :
    Continuous (mapToUnitsPow₀_aux K) := by
  unfold mapToUnitsPow₀_aux
  refine continuous_pi_iff.mpr fun w ↦ ?_
  by_cases hw : w = w₀
  · simp_rw [dif_pos hw]
    fun_prop
  · simp_rw [dif_neg hw]
    fun_prop

variable {K}

/-- DOCSTRING -/
def equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀} := by
  classical
  refine Fintype.equivOfCardEq ?_
  rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank]

variable (K)

open Classical in
/-- DOCSTRING -/
-- This cannot be a `PartiaHomeomorph` because the target is not an open set
def mapToUnitsPow₀ :
    PartialEquiv ({w : InfinitePlace K // w ≠ w₀} → ℝ) (realSpace K) :=
  (((basisUnitLattice K).ofZLatticeBasis ℝ).reindex
    equivFinRank).equivFun.symm.toEquiv.toPartialEquiv.trans (mapToUnitsPow₀_aux K)

theorem mapToUnitsPow₀_source :
    (mapToUnitsPow₀ K).source = Set.univ := by simp [mapToUnitsPow₀, mapToUnitsPow₀_aux]

theorem mapToUnitsPow₀_target :
    (mapToUnitsPow₀ K).target = {x | (∀ w, 0 < x w) ∧ mixedEmbedding.norm (realToMixed x) = 1} := by
  rw [mapToUnitsPow₀, mapToUnitsPow₀_aux]
  dsimp
  ext x
  simp_rw [Set.inter_univ, Set.mem_inter_iff, Set.mem_setOf, and_congr_right_iff]
  intro hx
  rw [← Real.exp_injective.eq_iff, Real.exp_zero, Real.exp_sum, norm_realToMixed]
  refine Eq.congr (Finset.prod_congr rfl fun _ _ ↦ ?_) rfl
  rw [← Real.log_rpow (hx _), Real.exp_log (Real.rpow_pos_of_pos (hx _) _), Real.norm_eq_abs,
    abs_of_pos (hx _), Real.rpow_natCast]

variable {K}

theorem norm_mapToUnitsPow₀ (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    mixedEmbedding.norm (realToMixed (mapToUnitsPow₀ K c)) = 1 := by
  suffices mapToUnitsPow₀ K c ∈ (mapToUnitsPow₀ K).target by
    rw [mapToUnitsPow₀_target] at this
    exact this.2
  refine PartialEquiv.map_source (mapToUnitsPow₀ K) ?_
  rw [mapToUnitsPow₀_source]
  exact trivial

theorem mapToUnitsPow₀_pos (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) (w : InfinitePlace K) :
    0 < mapToUnitsPow₀ K c w := by
  suffices mapToUnitsPow₀ K c ∈ (mapToUnitsPow₀ K).target by
    rw [mapToUnitsPow₀_target] at this
    exact this.1 w
  refine PartialEquiv.map_source (mapToUnitsPow₀ K) ?_
  rw [mapToUnitsPow₀_source]
  exact trivial

open Classical in
theorem mapToUnitsPow₀_symm_prod_fundSystem_rpow (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    (mapToUnitsPow₀ K).symm (fun w ↦ ∏ i, w (fundSystem K (equivFinRank.symm i)) ^ c i) = c := by
  ext
  simp_rw [mapToUnitsPow₀, PartialEquiv.coe_trans_symm, Equiv.toPartialEquiv_symm_apply,
    LinearEquiv.coe_toEquiv_symm, LinearEquiv.symm_symm, Function.comp_apply,
    mapToUnitsPow₀_aux_symm_apply, EquivLike.coe_coe, Basis.equivFun_apply, Basis.repr_reindex,
    Real.log_prod _ _ (fun _ _ ↦ (Real.rpow_pos_of_pos (Units.pos_at_place _ _) _).ne'),
    Real.log_rpow (Units.pos_at_place _ _), mul_sum, mul_left_comm, ← logEmbedding_component,
    logEmbedding_fundSystem, ← sum_fn, _root_.map_sum, ← smul_eq_mul, ← Pi.smul_def,
    _root_.map_smul, Finsupp.mapDomain_equiv_apply, sum_apply', Finsupp.coe_smul, Pi.smul_apply,
    Basis.ofZLatticeBasis_repr_apply, Basis.repr_self, smul_eq_mul, Finsupp.single_apply,
    Int.cast_ite, mul_ite, Int.cast_zero, mul_zero, EmbeddingLike.apply_eq_iff_eq, sum_ite_eq',
    mem_univ, if_true, Int.cast_one, mul_one]

open Classical in
theorem mapToUnitsPow₀_apply (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    mapToUnitsPow₀ K c = fun w ↦ ∏ i, w (fundSystem K (equivFinRank.symm i)) ^ c i := by
  refine (PartialEquiv.eq_symm_apply _ (by trivial) ?_).mp
    (mapToUnitsPow₀_symm_prod_fundSystem_rpow c).symm
  rw [mapToUnitsPow₀_target]
  refine ⟨?_, norm_realToMixed_prod_units_rpow c _⟩
  exact fun _ ↦ Finset.prod_pos fun _ _ ↦ Real.rpow_pos_of_pos (Units.pos_at_place _ _) _

open Classical in
theorem mapToUnitsPow₀_symm_apply_of_norm_one {x : InfinitePlace K → ℝ}
    (hx : mixedEmbedding.norm (realToMixed x) = 1) :
    (mapToUnitsPow₀ K).symm x = (((basisUnitLattice K).ofZLatticeBasis ℝ).reindex
      equivFinRank).equivFun (logMap (realToMixed x)) := by
  rw [mapToUnitsPow₀, PartialEquiv.coe_trans_symm, Equiv.toPartialEquiv_symm_apply,
    LinearEquiv.coe_toEquiv_symm, LinearEquiv.symm_symm, EquivLike.coe_coe, Function.comp_apply]
  congr with x
  rw [logMap_apply_of_norm_one hx, mapToUnitsPow₀_aux, PartialEquiv.coe_symm_mk,
    normAtPlace_realToMixed, Real.norm_eq_abs, Real.log_abs]

variable (K) in
open Classical in
theorem continuous_mapToUnitsPow₀ :
    Continuous (mapToUnitsPow₀ K) := (continuous_mapToUnitsPow₀_aux K).comp <|
  LinearEquiv.continuous_symm _ (continuous_equivFun_basis _)

open Classical in
/-- DOCSTRING -/
abbrev mapToUnitsPow_single (c : realSpace K) : InfinitePlace K → (realSpace K) :=
  fun i ↦ if hi : i = w₀ then fun _ ↦ |c w₀| else
    fun w ↦ (w (fundSystem K (equivFinRank.symm ⟨i, hi⟩))) ^ (c i)

open Classical in
theorem mapToUnitsPow₀_eq_prod_single (c : realSpace K) (w : InfinitePlace K) :
    mapToUnitsPow₀ K (fun w ↦ c w.val) w =
      ∏ i ∈ univ.erase w₀, mapToUnitsPow_single c i w := by
  rw [mapToUnitsPow₀_apply, Finset.prod_subtype (Finset.univ.erase w₀)
    (fun w ↦ (by aesop : w ∈ univ.erase w₀ ↔ w ≠ w₀))]
  exact Finset.prod_congr rfl fun w _ ↦ by rw [mapToUnitsPow_single, dif_neg w.prop]

theorem prod_mapToUnitsPow_single (c : realSpace K) :
    ∏ i, mapToUnitsPow_single c i = |c w₀| • mapToUnitsPow₀ K (fun w ↦ c w.val) := by
  classical
  ext
  rw [Pi.smul_apply, mapToUnitsPow₀_eq_prod_single, ← Finset.univ.mul_prod_erase _
    (Finset.mem_univ w₀), mapToUnitsPow_single, dif_pos rfl, smul_eq_mul, Pi.mul_apply, prod_apply]

variable (K)

open Classical in
/-- DOCSTRING -/
@[simps source target]
def mapToUnitsPow : PartialHomeomorph (realSpace K) (realSpace K) where
  toFun c := ∏ i, mapToUnitsPow_single c i
  invFun x w :=
    if hw : w = w₀ then mixedEmbedding.norm (realToMixed x) ^ (finrank ℚ K : ℝ)⁻¹ else
      (((basisUnitLattice K).ofZLatticeBasis ℝ).reindex
        equivFinRank).equivFun (logMap (realToMixed x)) ⟨w, hw⟩
  source := {x | 0 < x w₀}
  target := {x | ∀ w, 0 < x w}
  map_source' _ h _ := by
    simp_rw [prod_mapToUnitsPow_single, Pi.smul_apply, smul_eq_mul]
    exact mul_pos (abs_pos.mpr h.ne') (mapToUnitsPow₀_pos _ _)
  map_target' x hx := by
    refine Set.mem_setOf.mpr ?_
    dsimp only
    rw [dif_pos rfl]
    exact Real.rpow_pos_of_pos (pos_norm_realToMixed (fun w ↦ (hx w).ne')) _
  left_inv' _ h := by
    dsimp only
    ext w
    by_cases hw : w = w₀
    · rw [hw, dif_pos rfl, prod_mapToUnitsPow_single, map_smul, mixedEmbedding.norm_smul,
        norm_mapToUnitsPow₀, mul_one, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _),
        mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (finrank_pos).ne'), Real.rpow_one, abs_of_nonneg
          (abs_nonneg _), abs_of_pos (by convert h)]
    · rw [dif_neg hw, prod_mapToUnitsPow_single, map_smul, logMap_real_smul
        (by rw [norm_mapToUnitsPow₀]; exact one_ne_zero) (abs_ne_zero.mpr (ne_of_gt h)),
        ← mapToUnitsPow₀_symm_apply_of_norm_one, PartialEquiv.left_inv _
        (by rw [mapToUnitsPow₀_source]; trivial)]
      rw [mapToUnitsPow₀_apply]
      exact norm_realToMixed_prod_units_rpow _ _
  right_inv' x hx := by
    have h₀ : mixedEmbedding.norm
        (realToMixed (mixedEmbedding.norm (realToMixed x) ^ (- (finrank ℚ K : ℝ)⁻¹) • x)) = 1 := by
      rw [map_smul, norm_smul, ← abs_pow, ← Real.rpow_natCast, ← Real.rpow_mul, neg_mul,
        inv_mul_cancel₀, Real.rpow_neg_one, abs_of_nonneg, inv_mul_cancel₀]
      · rw [mixedEmbedding.norm_ne_zero_iff]
        intro w
        rw [normAtPlace_realToMixed, Real.norm_eq_abs, abs_ne_zero]
        exact (hx w).ne'
      refine inv_nonneg.mpr (mixedEmbedding.norm_nonneg _)
      rw [Nat.cast_ne_zero]
      exact finrank_pos.ne'
      exact mixedEmbedding.norm_nonneg _
    have hx' : ∀ w, x w ≠ 0 := fun w ↦ (hx w).ne'
    dsimp only
    rw [prod_mapToUnitsPow_single, dif_pos rfl]
    conv_lhs =>
      enter [2, 2, w]
      rw [dif_neg w.prop]
    ext w
    rw [Pi.smul_apply, ← logMap_real_smul]
    rw [← _root_.map_smul]
    rw [← mapToUnitsPow₀_symm_apply_of_norm_one h₀]
    rw [PartialEquiv.right_inv, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [abs_of_nonneg, Real.rpow_neg, mul_inv_cancel_left₀]
    · refine Real.rpow_ne_zero_of_pos ?_ _
      exact pos_norm_realToMixed hx'
    · exact mixedEmbedding.norm_nonneg (realToMixed x)
    · refine Real.rpow_nonneg ?_ _
      exact mixedEmbedding.norm_nonneg (realToMixed x)
    · rw [mapToUnitsPow₀_target]
      refine ⟨fun w ↦ ?_, h₀⟩
      exact mul_pos (Real.rpow_pos_of_pos (pos_norm_realToMixed hx') _) (hx w)
    · exact ne_of_gt (pos_norm_realToMixed hx')
    · refine Real.rpow_ne_zero_of_pos ?_ _
      exact pos_norm_realToMixed hx'
  open_source := isOpen_lt continuous_const (continuous_apply w₀)
  open_target := by
    convert_to IsOpen (⋂ w, {x : InfinitePlace K → ℝ | 0 < x w})
    · ext; simp
    · exact isOpen_iInter_of_finite fun w ↦ isOpen_lt continuous_const (continuous_apply w)
  continuousOn_toFun := by
    simp_rw [prod_mapToUnitsPow_single]
    exact ContinuousOn.smul (by fun_prop) <|
      (continuous_mapToUnitsPow₀ K).comp_continuousOn' (by fun_prop)
  continuousOn_invFun := by
    simp only
    rw [continuousOn_pi]
    intro w
    by_cases hw : w = w₀
    · simp_rw [hw, dite_true]
      refine Continuous.continuousOn ?_
      refine Continuous.rpow_const ?_ ?_
      · refine Continuous.comp' ?_ ?_
        exact mixedEmbedding.continuous_norm K
        exact ContinuousLinearMap.continuous realToMixed
      · intro _
        right
        rw [inv_nonneg]
        exact Nat.cast_nonneg' (finrank ℚ K)
    · simp_rw [dif_neg hw]
      refine Continuous.comp_continuousOn' (continuous_apply _) <|
        (continuous_equivFun_basis _).comp_continuousOn' ?_
      refine ContinuousOn.comp'' (continuousOn_logMap K) ?_ ?_
      refine Continuous.continuousOn ?_
      exact ContinuousLinearMap.continuous realToMixed
      intro x hx
      refine ne_of_gt ?_
      exact pos_norm_realToMixed (fun w ↦ (hx w).ne')

theorem mapToUnitsPow_apply (c : realSpace K) :
    mapToUnitsPow K c = ∏ i, mapToUnitsPow_single c i := rfl

theorem mapToUnitsPow_apply' (c : realSpace K) :
    mapToUnitsPow K c = |c w₀| • mapToUnitsPow₀ K (fun w ↦ c w.val) := by
  rw [mapToUnitsPow_apply, prod_mapToUnitsPow_single]

theorem mapToUnitsPow_zero_iff {c : InfinitePlace K → ℝ} :
    mapToUnitsPow K c = 0 ↔ c w₀ = 0 := by
  rw [mapToUnitsPow_apply', smul_eq_zero, abs_eq_zero, or_iff_left]
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  refine Function.ne_iff.mpr ⟨w, ?_⟩
  convert (mapToUnitsPow₀_pos (fun i ↦ c i) w).ne'

open ContinuousLinearMap

/-- DOCSTRING -/
abbrev mapToUnitsPow_fDeriv_single (c : realSpace K) (i w : InfinitePlace K) :
    (realSpace K) →L[ℝ] ℝ := by
  classical
  exact if hi : i = w₀ then proj w₀ else
    (w (fundSystem K (equivFinRank.symm ⟨i, hi⟩)) ^ c i *
      (w (fundSystem K (equivFinRank.symm ⟨i, hi⟩))).log) • proj i

theorem hasFDeriv_mapToUnitsPow_single (c : realSpace K) (i w : InfinitePlace K)
    (hc : 0 ≤ c w₀) :
    HasFDerivWithinAt (fun x ↦ mapToUnitsPow_single x i w)
      (mapToUnitsPow_fDeriv_single K c i w) {x | 0 ≤ x w₀} c := by
  unfold mapToUnitsPow_single mapToUnitsPow_fDeriv_single
  split_ifs
  · refine HasFDerivWithinAt.congr' (hasFDerivWithinAt_apply w₀ c _) ?_ hc
    exact fun _ h ↦ by simp_rw [abs_of_nonneg (Set.mem_setOf.mp h)]
  · exact HasFDerivWithinAt.const_rpow (hasFDerivWithinAt_apply i c _) <| pos_iff.mpr (by aesop)

open Classical in
/-- DOCSTRING -/
abbrev mapToUnitsPow_jacobianCoeff (w i : InfinitePlace K) : (realSpace K) → ℝ :=
  fun c ↦ if hi : i = w₀ then 1 else |c w₀| * (w (fundSystem K (equivFinRank.symm ⟨i, hi⟩))).log

/-- DOCSTRING -/
abbrev mapToUnitsPow_jacobian (c : realSpace K) : (realSpace K) →L[ℝ] InfinitePlace K → ℝ :=
  pi fun i ↦ (mapToUnitsPow₀ K (fun w ↦ c w) i •
    ∑ w, (mapToUnitsPow_jacobianCoeff K i w c) • proj w)

theorem hasFDeriv_mapToUnitsPow (c : InfinitePlace K → ℝ) (hc : 0 ≤ c w₀) :
    HasFDerivWithinAt (mapToUnitsPow K) (mapToUnitsPow_jacobian K c) {x | 0 ≤ x w₀} c := by
  classical
  refine hasFDerivWithinAt_pi'.mpr fun w ↦ ?_
  simp_rw [mapToUnitsPow_apply, Finset.prod_apply]
  convert HasFDerivWithinAt.finset_prod fun i _ ↦ hasFDeriv_mapToUnitsPow_single K c i w hc
  rw [ContinuousLinearMap.proj_pi, Finset.smul_sum]
  refine Fintype.sum_congr _ _ fun i ↦ ?_
  by_cases hi : i = w₀
  · simp_rw [hi, mapToUnitsPow_jacobianCoeff, dite_true, one_smul, dif_pos,
      mapToUnitsPow₀_eq_prod_single]
  · rw [mapToUnitsPow₀_eq_prod_single, mapToUnitsPow_jacobianCoeff, dif_neg hi, smul_smul,
      ← mul_assoc, show |c w₀| = mapToUnitsPow_single c w₀ w by simp_rw [dif_pos rfl],
      Finset.prod_erase_mul _ _ (Finset.mem_univ w₀), mapToUnitsPow_fDeriv_single, dif_neg hi,
      smul_smul,  ← mul_assoc, show w (algebraMap (𝓞 K) K
        (fundSystem K (equivFinRank.symm ⟨i, hi⟩))) ^ c i = mapToUnitsPow_single c i w by
      simp_rw [dif_neg hi], Finset.prod_erase_mul _ _ (Finset.mem_univ i)]

open Classical in
theorem prod_mapToUnitsPow₀(c : {w : InfinitePlace K // w ≠ w₀} → ℝ) :
    ∏ w : InfinitePlace K, mapToUnitsPow₀ K c w =
      (∏ w : {w : InfinitePlace K // IsComplex w}, mapToUnitsPow₀ K c w)⁻¹ := by
  have : ∏ w : { w  // IsComplex w}, (mapToUnitsPow₀ K) c w.val ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w _ ↦ ne_of_gt (mapToUnitsPow₀_pos c w)
  rw [← mul_eq_one_iff_eq_inv₀ this]
  convert norm_mapToUnitsPow₀ c
  simp_rw [norm_realToMixed, ← Fintype.prod_subtype_mul_prod_subtype (fun w ↦ IsReal w)]
  rw [← (Equiv.subtypeEquivRight (fun _ ↦ not_isReal_iff_isComplex)).prod_comp]
  simp_rw [Equiv.subtypeEquivRight_apply_coe]
  rw [mul_assoc, ← sq, ← Finset.prod_pow]
  congr with w
  · rw [Real.norm_eq_abs, abs_of_pos (mapToUnitsPow₀_pos c _), mult, if_pos w.prop, pow_one]
  · rw [Real.norm_eq_abs, abs_of_pos (mapToUnitsPow₀_pos c _), mult, if_neg w.prop]

open Classical in
theorem mapToUnitsPow_jacobian_det {c : realSpace K} (hc : 0 ≤ c w₀) :
    |(mapToUnitsPow_jacobian K c).det| =
      (∏ w : {w : InfinitePlace K // w.IsComplex }, mapToUnitsPow₀ K (fun w ↦ c w) w)⁻¹ *
        2⁻¹ ^ NrComplexPlaces K * |c w₀| ^ (rank K) * (finrank ℚ K) * regulator K := by
  have : LinearMap.toMatrix' (mapToUnitsPow_jacobian K c).toLinearMap =
      Matrix.of fun w i ↦ mapToUnitsPow₀ K (fun w ↦ c w) w *
        mapToUnitsPow_jacobianCoeff K w i c := by
    ext
    simp_rw [mapToUnitsPow_jacobian, ContinuousLinearMap.coe_pi, ContinuousLinearMap.coe_smul,
      ContinuousLinearMap.coe_sum, LinearMap.toMatrix'_apply, LinearMap.pi_apply,
      LinearMap.smul_apply, LinearMap.coeFn_sum, Finset.sum_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.of_apply]
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix', this]
  rw [Matrix.det_mul_column, prod_mapToUnitsPow₀, ← Matrix.det_transpose]
  simp_rw [mapToUnitsPow_jacobianCoeff]
  rw [mul_assoc, finrank_mul_regulator_eq_det K w₀ equivFinRank.symm]
  have : |c w₀| ^ rank K = |∏ w : InfinitePlace K, if w = w₀ then 1 else c w₀| := by
    rw [Finset.prod_ite, Finset.prod_const_one, Finset.prod_const, one_mul, abs_pow]
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, rank]
  rw [this, mul_assoc, ← abs_mul, ← Matrix.det_mul_column]
  have : (2 : ℝ)⁻¹ ^ NrComplexPlaces K = |∏ w : InfinitePlace K, (mult w : ℝ)⁻¹| := by
    rw [Finset.abs_prod]
    simp_rw [mult, Nat.cast_ite, Nat.cast_one, Nat.cast_ofNat, apply_ite, abs_inv, abs_one, inv_one,
      Nat.abs_ofNat, Finset.prod_ite, Finset.prod_const_one, Finset.prod_const, one_mul]
    rw [Finset.filter_not, Finset.card_univ_diff, ← Fintype.card_subtype]
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces, ← NrRealPlaces, add_tsub_cancel_left]
  rw [this, mul_assoc, ← abs_mul, ← Matrix.det_mul_row, abs_mul]
  congr
  · rw [abs_eq_self.mpr]
    rw [inv_nonneg]
    exact Finset.prod_nonneg fun _ _ ↦ (mapToUnitsPow₀_pos _ _).le
  · ext
    simp only [Matrix.transpose_apply, Matrix.of_apply, ite_mul, one_mul, mul_ite]
    split_ifs
    · rw [inv_mul_cancel₀ mult_coe_ne_zero]
    · rw [← mul_assoc, mul_comm _ (c w₀), mul_assoc, inv_mul_cancel_left₀ mult_coe_ne_zero,
        abs_eq_self.mpr hc]

open MeasureTheory

private theorem setLIntegral_mapToUnitsPow_aux₀ {s : Set (realSpace K)} (hs : s ⊆ {x | 0 ≤ x w₀}) :
    s \ (s ∩ {x | 0 < x w₀}) ⊆ {x | x w₀ = 0} := by
  refine fun _ h ↦ eq_of_ge_of_not_gt (hs h.1) ?_
  have := h.2
  simp_rw [Set.mem_inter_iff, not_and, h.1, true_implies] at this
  exact this

private theorem setLIntegral_mapToUnitsPow_aux₁ :
    volume {x : realSpace K | x w₀ = 0} = 0 := by
  let A : AffineSubspace ℝ (realSpace K) :=
    Submodule.toAffineSubspace (Submodule.mk ⟨⟨{x | x w₀ = 0}, by aesop⟩, rfl⟩ (by aesop))
  convert Measure.addHaar_affineSubspace volume A fun h ↦ ?_
  have : 1 ∈ A := h ▸ Set.mem_univ _
  simp [A] at this

private theorem setLIntegral_mapToUnitsPow_aux₂ {s : Set (realSpace K)} (hs : s ⊆ {x | 0 ≤ x w₀}) :
    (mapToUnitsPow K) '' s =ᵐ[volume] (mapToUnitsPow K) '' (s ∩ {x | 0 < x w₀}) := by
  refine measure_symmDiff_eq_zero_iff.mp ?_
  rw [symmDiff_of_ge (Set.image_mono Set.inter_subset_left)]
  have : mapToUnitsPow K '' s \ mapToUnitsPow K '' (s ∩ {x | 0 < x w₀}) ⊆ { 0 } := by
    rintro _ ⟨⟨x, hx, rfl⟩, hx'⟩
    have hx'' : x ∉ s ∩ {x | 0 < x w₀} := fun h ↦ hx' (Set.mem_image_of_mem _ h)
    simp_rw [Set.mem_inter_iff, Set.mem_setOf_eq, not_and] at hx''
    rw [Set.mem_singleton_iff, mapToUnitsPow_zero_iff]
    refine eq_of_ge_of_not_gt (hs hx) (hx'' hx)
  exact measure_mono_null this (measure_singleton _)

open ENNReal Classical in
theorem setLIntegral_mapToUnitsPow {s : Set (realSpace K)} (hs₀ : MeasurableSet s)
    (hs₁ : s ⊆ {x | 0 ≤ x w₀}) (f : (InfinitePlace K → ℝ) → ℝ≥0∞) :
    ∫⁻ x in (mapToUnitsPow K) '' s, f x =
      (2 : ℝ≥0∞)⁻¹ ^ NrComplexPlaces K * ENNReal.ofReal (regulator K) * (finrank ℚ K) *
      ∫⁻ x in s, ENNReal.ofReal |x w₀| ^ rank K *
        ENNReal.ofReal (∏ i : {w : InfinitePlace K // IsComplex w},
          (mapToUnitsPow₀ K (fun w ↦ x w) i))⁻¹ * f (mapToUnitsPow K x) := by
  rw [setLIntegral_congr (setLIntegral_mapToUnitsPow_aux₂ K hs₁)]
  have : s =ᵐ[volume] (s ∩ {x | 0 < x w₀} : Set (realSpace K)) := by
    refine measure_symmDiff_eq_zero_iff.mp <|
      measure_mono_null ?_ (setLIntegral_mapToUnitsPow_aux₁ K)
    rw [symmDiff_of_ge Set.inter_subset_left]
    exact setLIntegral_mapToUnitsPow_aux₀ K hs₁
  rw [setLIntegral_congr this]
  have h : MeasurableSet (s ∩ {x | 0 < x w₀}) :=
    hs₀.inter (measurableSet_lt measurable_const (measurable_pi_apply w₀))
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume h (fun c hc ↦
    HasFDerivWithinAt.mono (hasFDeriv_mapToUnitsPow K c (hs₁ (Set.mem_of_mem_inter_left hc)))
    (Set.inter_subset_left.trans hs₁)) ((mapToUnitsPow K).injOn.mono Set.inter_subset_right)]
  rw [setLIntegral_congr_fun h
    (ae_of_all volume fun c hc ↦ by rw [mapToUnitsPow_jacobian_det K
    (hs₁ (Set.mem_of_mem_inter_left hc))]), ← lintegral_const_mul']
  · congr with x
    -- This will be useful for positivity goals
    have : 0 ≤ (∏ w : {w : InfinitePlace K // IsComplex w}, mapToUnitsPow₀ K (fun w ↦ x w) w)⁻¹ :=
      inv_nonneg.mpr <| Finset.prod_nonneg fun w _ ↦ (mapToUnitsPow₀_pos _ _).le
    rw [ofReal_mul (by positivity), ofReal_mul (by positivity), ofReal_mul (by positivity),
      ofReal_mul (by positivity), ofReal_natCast, ofReal_pow (by positivity), ofReal_pow
      (by positivity), ofReal_inv_of_pos zero_lt_two, ofReal_ofNat]
    ring
  · exact mul_ne_top (mul_ne_top (pow_ne_top (inv_ne_top.mpr two_ne_zero)) ofReal_ne_top)
      (natCast_ne_top _)

end mapToUnitsPow

namespace fundamentalCone

variable [NumberField K]

/-- DOCSTRING -/
abbrev normLessThanOne : Set (mixedSpace K) :=
  {x | x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ 1}

theorem measurableSet_normLessThanOne :
    MeasurableSet (normLessThanOne K) :=
  -- MeasurableSet.inter (measurableSet K) <|
  --   measurableSet_le (mixedEmbedding.continuous_norm K).measurable measurable_const
  sorry

theorem isBounded_normLessThanOne :
    IsBounded (normLessThanOne K) := by
  sorry

open MeasureTheory

open Classical in
theorem volume_normLessThanOne :
    volume (normLessThanOne K) =
      2 ^ NrRealPlaces K * NNReal.pi ^ NrComplexPlaces K * (regulator K).toNNReal := by
  sorry

open Classical in
theorem volume_frontier_normLessThanOne :
    volume (frontier (normLessThanOne K)) = 0 := by
  sorry

end NumberField.mixedEmbedding.fundamentalCone
