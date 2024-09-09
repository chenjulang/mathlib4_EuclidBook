/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Fundamental Cone

Let `K` be a number field of signature `(r₁, r₂)`. We define an action of the units `(𝓞 K)ˣ` on the
space `ℝ^r₁ × ℂ^r₂` via the `mixedEmbedding`. The fundamental cone is a cone in `ℝ^r₁ × ℂ^r₂` that
is a fundamental domain for the action of `(𝓞 K)ˣ` up to roots of unity.

## Main definitions and results

* `NumberField.mixedEmbedding.unitSMul`: the action of `(𝓞 K)ˣ` on `ℝ^r₁ × ℂ^r₂` defined, for
`u : (𝓞 K)ˣ`, by multiplication component by component with `mixedEmbedding K u`.

* `NumberField.mixedEmbedding.fundamentalCone`: a cone in `ℝ^r₁ × ℂ^r₂` --that is a subset stable
by multiplication by a real number, see `smul_mem_of_mem`--, that is also a fundamental domain for
the action of `(𝓞 K)ˣ` up to roots of unity, see `exists_unitSMul_me` and
`torsion_unitSMul_mem_of_mem`.

## Tags
number field, canonical embedding, principal ideals
 -/

variable (K : Type*) [Field K]

namespace NumberField.mixedEmbedding

open NumberField NumberField.InfinitePlace

noncomputable section UnitSMul

/-- The action of `(𝓞 K)ˣ` on the mixed space `ℝ^r₁ × ℂ^r₂` defined, for `u : (𝓞 K)ˣ`, by
multiplication component by component with `mixedEmbedding K u`. -/
@[simps]
instance unitSMul : SMul (𝓞 K)ˣ (mixedSpace K) where
  smul := fun u x ↦ (mixedEmbedding K u) * x

instance : MulAction (𝓞 K)ˣ (mixedSpace K) where
  one_smul := fun _ ↦ by simp_rw [unitSMul_smul, Units.coe_one, map_one, one_mul]
  mul_smul := fun _ _ _ ↦ by simp_rw [unitSMul_smul, Units.coe_mul, map_mul, mul_assoc]

instance : SMulZeroClass (𝓞 K)ˣ (mixedSpace K) where
  smul_zero := fun _ ↦ by simp_rw [unitSMul_smul, mul_zero]

theorem unitSMul_eq_zero (u : (𝓞 K)ˣ) (x : mixedSpace K) :
    u • x = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext w
    · have := congr_fun (congr_arg Prod.fst h) w
      rw [unitSMul_smul, Prod.fst_mul, Pi.mul_apply, Prod.fst_zero, Pi.zero_apply, mul_eq_zero]
        at this
      refine this.resolve_left (by simp only [mixedEmbedding_apply_ofIsReal, map_eq_zero,
        RingOfIntegers.coe_eq_zero_iff, Units.ne_zero, not_false_eq_true])
    · have := congr_fun (congr_arg Prod.snd h) w
      rw [unitSMul_smul, Prod.snd_mul, Pi.mul_apply, Prod.snd_zero, Pi.zero_apply, mul_eq_zero]
        at this
      refine this.resolve_left (by simp only [mixedEmbedding_apply_ofIsComplex, map_eq_zero,
        RingOfIntegers.coe_eq_zero_iff, Units.ne_zero, not_false_eq_true])
  · rw [h, smul_zero]

variable [NumberField K]

theorem unitSMul_eq_iff_mul_eq {x y : (𝓞 K)} {u : (𝓞 K)ˣ} :
    u • mixedEmbedding K x = mixedEmbedding K y ↔ u * x = y := by
  rw [unitSMul_smul, ← map_mul, Function.Injective.eq_iff, ← RingOfIntegers.coe_eq_algebraMap,
    ← map_mul, ← RingOfIntegers.ext_iff]
  exact mixedEmbedding_injective K

theorem norm_unitSMul (u : (𝓞 K)ˣ) (x : mixedSpace K) :
    mixedEmbedding.norm (u • x) = mixedEmbedding.norm x := by
  rw [unitSMul_smul, map_mul, norm_unit, one_mul]

end UnitSMul

noncomputable section logMap

open NumberField.Units NumberField.Units.dirichletUnitTheorem FiniteDimensional

variable [NumberField K] {K}

open Classical in
/-- The map from the mixed space to `{w : InfinitePlace K // w ≠ w₀} → ℝ` (with `w₀` the fixed
place from the proof of Dirichlet's theorem: see `NumberField.Units.dirichletUnitTheorem.w₀`)
defined in such way that: 1) it factors the map `logEmbedding`, see `logMap_eq_logEmbedding`;
2) it is constant on the lines `{c • x | c ∈ ℝ}`, see `logMap_smul`. -/
def logMap (x : mixedSpace K) : {w : InfinitePlace K // w ≠ w₀} → ℝ := fun w ↦
  mult w.val * (Real.log (normAtPlace w.val x) -
    Real.log (mixedEmbedding.norm x) * (finrank ℚ K : ℝ)⁻¹)

-- theorem logMap_apply (x : mixedSpace K) (w : {w : InfinitePlace K // w ≠ w₀}) :
--     logMap x w = mult w.val * (Real.log (normAtPlace w.val x) -
--       Real.log (mixedEmbedding.norm x) * (finrank ℚ K : ℝ)⁻¹) := rfl

-- @[simp]
-- theorem logMap_zero : logMap (0 : mixedSpace K) = 0 := by
--   ext
--   rw [logMap, map_zero, map_zero, Real.log_zero, zero_mul, sub_self, mul_zero, Pi.zero_apply]

-- @[simp]
-- theorem logMap_one : logMap (1 : mixedSpace K) = 0 := by
--   ext
--   rw [logMap, map_one, show 1 = mixedEmbedding K (1 : (𝓞 K)ˣ) by
--       rw [Units.val_one, map_one, map_one], norm_unit, Real.log_one, zero_mul, sub_self,
--     mul_zero, Pi.zero_apply]

theorem logMap_mul {x y : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0)
    (hy : mixedEmbedding.norm y ≠ 0) :
    logMap (x * y) = logMap x + logMap y := by
  ext w
  simp_rw [Pi.add_apply, logMap]
  rw [map_mul, map_mul, Real.log_mul, Real.log_mul hx hy, add_mul]
  · ring
  · exact mixedEmbedding.norm_ne_zero_iff.mp hx w
  · exact mixedEmbedding.norm_ne_zero_iff.mp hy w

-- theorem logMap_prod {ι : Type*} (s : Finset ι) {x : ι → (mixedSpace K)}
--     (hx : ∀ i ∈ s, mixedEmbedding.norm (x i) ≠ 0) :
--     logMap (∏ i ∈ s, x i) = ∑ i ∈ s, logMap (x i) := by
--   induction s using Finset.cons_induction with
--   | empty => simp
--   | cons i s hi h_ind =>
--       rw [Finset.prod_cons, Finset.sum_cons, logMap_mul, h_ind]
--       · exact fun _ h ↦ hx _ (Finset.mem_cons_of_mem h)
--       · exact hx i (Finset.mem_cons_self i s)
--       · rw [map_prod, Finset.prod_ne_zero_iff]
--         exact fun _ h ↦ hx _ (Finset.mem_cons_of_mem h)

-- theorem logMap_eq_logEmbedding (u : (𝓞 K)ˣ) :
--     logMap (mixedEmbedding K u) = logEmbedding K u := by
--   ext
--   simp_rw [logMap, mixedEmbedding.norm_unit, Real.log_one, zero_mul, sub_zero, normAtPlace_apply,
--     logEmbedding_component]

-- theorem logMap_unitSMul (u : (𝓞 K)ˣ) {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) :
--     logMap (u • x) = logEmbedding K u + logMap x := by
--   rw [unitSMul_smul, logMap_mul (by rw [norm_unit]; norm_num) hx, logMap_eq_logEmbedding]

-- theorem logMap_torsion_unitSMul (x : mixedSpace K) {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K) :
--     logMap (ζ • x) = logMap x := by
--   ext
--   simp_rw [logMap, unitSMul_smul, map_mul, norm_eq_norm, Units.norm, Rat.cast_one, one_mul,
--     normAtPlace_apply, (mem_torsion K).mp hζ, one_mul]

theorem logMap_smul {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) {c : ℝ} (hc : c ≠ 0) :
    logMap (c • x) = logMap x := by
  rw [show c • x = ((fun _ ↦ c, fun _ ↦ c) : (mixedSpace K)) * x by rfl, logMap_mul _ hx,
    add_left_eq_self]
  · ext
    have hr : (finrank ℚ K : ℝ) ≠ 0 :=  Nat.cast_ne_zero.mpr (ne_of_gt finrank_pos)
    simp_rw [logMap, normAtPlace_real, norm_real, Real.log_pow, mul_comm, inv_mul_cancel_left₀ hr,
      sub_self, zero_mul, Pi.zero_apply]
  · rw [norm_real]
    exact pow_ne_zero _ (abs_ne_zero.mpr hc)

-- theorem measurable_logMap :
--     Measurable (logMap : (mixedSpace K) → _) :=
--   measurable_pi_iff.mpr fun _ ↦
--     measurable_const.mul <| (continuous_normAtPlace _).measurable.log.sub
--       <| (mixedEmbedding.continuous_norm K).measurable.log.mul measurable_const

-- theorem continuousOn_logMap :
--     ContinuousOn (logMap : (mixedSpace K) → _) {x | mixedEmbedding.norm x ≠ 0} := by
--   refine continuousOn_pi.mpr fun w ↦ continuousOn_const.mul (ContinuousOn.sub ?_ ?_)
--   · exact Real.continuousOn_log.comp''  (continuous_normAtPlace _).continuousOn
--       fun _ hx ↦ mixedEmbedding.norm_ne_zero_iff.mp hx _
--   · exact ContinuousOn.mul
--       (Real.continuousOn_log.comp''  (mixedEmbedding.continuous_norm K).continuousOn
--         fun _ hx ↦ hx) continuousOn_const

-- theorem logMap_apply_of_norm_one {x : mixedSpace K} (hx : mixedEmbedding.norm x = 1)
--     {w : InfinitePlace K} (hw : w ≠ w₀) :
--     logMap x ⟨w, hw⟩ = mult w * Real.log (normAtPlace w x) := by
--   rw [logMap, hx, Real.log_one, zero_mul, sub_zero]

end logMap

open NumberField.Units NumberField.Units.dirichletUnitTheorem nonZeroDivisors BigOperators

variable [NumberField K]

open Classical in
/-- The fundamental cone is a cone in the mixed space --ie. a subset fixed by multiplication by
a scalar, see `smul_mem_of_mem`--, that is also a fundamental domain for the action of `(𝓞 K)ˣ` up
to roots of unity, see `exists_unitSMul_mem` and `torsion_unitSMul_mem_of_mem`. -/
def fundamentalCone : Set (mixedSpace K) :=
  logMap⁻¹' (ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ)) \
    {x | mixedEmbedding.norm x = 0}

namespace fundamentalCone

variable {K}

open Classical in
theorem mem_fundamentalCone {x : mixedSpace K} :
    x ∈ fundamentalCone K ↔
      logMap x ∈ ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ _) ∧
      mixedEmbedding.norm x ≠ 0 := Set.mem_def

theorem smul_mem_of_mem {x : mixedSpace K} (hx : x ∈ fundamentalCone K) {c : ℝ} (hc : c ≠ 0) :
    c • x ∈ fundamentalCone K := by
  refine ⟨?_, ?_⟩
  · rw [Set.mem_preimage, logMap_smul hx.2 hc]
    exact hx.1
  · rw [Set.mem_setOf_eq, mixedEmbedding.norm_smul, mul_eq_zero, not_or]
    exact ⟨pow_ne_zero _ (abs_ne_zero.mpr hc), hx.2⟩

theorem smul_mem_iff_mem {x : mixedSpace K} {c : ℝ} (hc : c ≠ 0) :
    c • x ∈ fundamentalCone K ↔ x ∈ fundamentalCone K := by
  refine ⟨fun h ↦ ?_, fun h ↦ smul_mem_of_mem h hc⟩
  convert smul_mem_of_mem h (inv_ne_zero hc)
  rw [eq_inv_smul_iff₀ hc]

noncomputable section integralPoint

variable (K)

/-- The set of images by `mixedEmbedding` of algebraic integers of `K` contained in the
fundamental cone. -/
def integralPoint : Set (mixedSpace K) :=
  fundamentalCone K ∩ mixedEmbedding.integerLattice K

variable {K}

/-- For `a : fundamentalCone K`, the unique non-zero algebraic integer which image by
`mixedEmbedding` is equal to `a`. -/
def preimageOfIntegralPoint (a : integralPoint K) : (𝓞 K)⁰ :=
  -- ⟨a.prop.2.choose_spec.1.choose, by
  --   simp_rw [mem_nonZeroDivisors_iff_ne_zero, ne_eq, RingOfIntegers.ext_iff,
  --     a.prop.2.choose_spec.1.choose_spec, ← (mixedEmbedding_injective K).eq_iff, map_zero,
  --     a.prop.2.choose_spec.2, integralPoint_ne_zero a, not_false_eq_true]⟩
  sorry

/-- The `mixedEmbedding.norm` of `a : integralPoint K` as a natural integer, see `intNorm_coe` . -/
def intNorm (a : integralPoint K) : ℕ := (Algebra.norm ℤ (preimageOfIntegralPoint a : 𝓞 K)).natAbs

@[simp]
theorem intNorm_coe (a : integralPoint K) :
    (intNorm a : ℝ) = mixedEmbedding.norm (a : mixedSpace K) := by
  sorry
--  rw [intNorm, Int.cast_natAbs, ← Rat.cast_intCast, Int.cast_abs, Algebra.coe_norm_int,
--    ← norm_eq_norm, mixedEmbedding_preimageOfIntegralPoint]

variable (K)

open Submodule Ideal

/-- For `n` positive, the number of `fundamentalCone.integralPoint K` of
norm `n` is equal to the number of principal ideals in `𝓞 K` of norm `n` multiplied by the number
of roots of unity in `K`. -/
theorem card_isPrincipal_norm_eq (n : ℕ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ | IsPrincipal (I : Ideal (𝓞 K)) ∧
      absNorm (I : Ideal (𝓞 K)) = n} * torsionOrder K =
        Nat.card {a : integralPoint K | intNorm a = n} := by
  -- rw [torsionOrder, PNat.mk_coe, ← Nat.card_eq_fintype_card, ← Nat.card_prod]
  -- exact Nat.card_congr (integralPointEquivNorm K n).symm
  sorry

theorem card_isPrincipal_norm_le (n : ℝ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ | IsPrincipal (I : Ideal (𝓞 K)) ∧
      absNorm (I : Ideal (𝓞 K)) ≤ n} * torsionOrder K =
        Nat.card {a : integralPoint K | intNorm a ≤ n} := by
  obtain hn | hn := le_or_gt 0 n
  · simp_rw [← Nat.le_floor_iff hn]
    sorry
  -- rw [torsionOrder, PNat.mk_coe, ← Nat.card_eq_fintype_card, ← Nat.card_prod]
  -- refine Nat.card_congr <| @Equiv.ofFiberEquiv _ (γ := Finset.Iic n) _
  --     (fun I ↦ ⟨absNorm (I.1 : Ideal (𝓞 K)), Finset.mem_Iic.mpr I.1.2.2⟩)
  --     (fun a ↦ ⟨intNorm a.1, Finset.mem_Iic.mpr a.2⟩) fun ⟨i, hi⟩ ↦ ?_
  -- simp_rw [Subtype.mk.injEq]
  -- calc
  --   _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 ≤ n} // absNorm I.1.1 = i}
  --         × torsion K := Equiv.prodSubtypeFstEquivSubtypeProd
  --   _ ≃ {I : (Ideal (𝓞 K))⁰ // (IsPrincipal I.1 ∧ absNorm I.1 ≤ n) ∧ absNorm I.1 = i}
  --         × torsion K := Equiv.prodCongrLeft fun _ ↦ (Equiv.subtypeSubtypeEquivSubtypeInter
  --     (p := fun I : (Ideal (𝓞 K))⁰ ↦ IsPrincipal I.1 ∧ absNorm I.1 ≤ n)
  --     (q := fun I ↦ absNorm I.1 = i))
  --   _ ≃ {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 = i ∧ absNorm I.1 ≤ n}
  --         × torsion K := Equiv.prodCongrLeft fun _ ↦ (Equiv.subtypeEquivRight fun _ ↦ by aesop)
  --   _ ≃ {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 = i} × torsion K :=
  --     Equiv.prodCongrLeft fun _ ↦ (Equiv.subtypeEquivRight fun _ ↦ by
  --     rw [and_iff_left_of_imp (a := absNorm _ = _) fun h ↦ Finset.mem_Iic.mp (h ▸ hi)])
  --   _ ≃ {a : integralPoint K // intNorm a = i} := (integralPointEquivNorm K i).symm
  --   _ ≃ {a : {a : integralPoint K // intNorm a ≤ n} // intNorm a.1 = i} :=
  --     (Equiv.subtypeSubtypeEquivSubtype fun h ↦ Finset.mem_Iic.mp (h ▸ hi)).symm
  · simp_rw [lt_iff_not_le.mp (lt_of_lt_of_le hn (Nat.cast_nonneg _)), and_false, Set.setOf_false,
      Nat.card_eq_fintype_card, Fintype.card_ofIsEmpty, zero_mul]

end integralPoint

end fundamentalCone

end NumberField.mixedEmbedding
