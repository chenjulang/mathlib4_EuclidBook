/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Covolume of ℤ-lattices

Let `E` be a finite dimensional real vector space with an inner product.

Let `L` be a `ℤ`-lattice `L` defined as a discrete `ℤ`-submodule of `E` that spans `E` over `ℝ`.

## Main definitions and results

* `ZLattice.covolume`: the covolume of `L` defined as the volume of an arbitrary fundamental
domain of `L`.

* `ZLattice.covolume_eq_measure_fundamentalDomain`: the covolume of `L` does not depend on the
choice of the fundamental domain of `L`.

* `ZLattice.covolume_eq_det`: if `L` is a lattice in `ℝ^n`, then its covolume is the absolute
value of the determinant of any `ℤ`-basis of `L`.

-/

noncomputable section

namespace ZLattice

open Submodule MeasureTheory FiniteDimensional MeasureTheory Module ZSpan

section General

variable (K : Type*) [NormedLinearOrderedField K] [HasSolidNorm K] [FloorRing K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]
variable [ProperSpace E] [MeasurableSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice K L]

/-- The covolume of a `ℤ`-lattice is the volume of some fundamental domain; see
`ZLattice.covolume_eq_volume` for the proof that the volume does not depend on the choice of
the fundamental domain. -/
def covolume (μ : Measure E := by volume_tac) : ℝ := (addCovolume L E μ).toReal

end General

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
variable (μ : Measure E := by volume_tac) [Measure.IsAddHaarMeasure μ]

theorem covolume_eq_measure_fundamentalDomain {F : Set E} (h : IsAddFundamentalDomain L F μ) :
    covolume L μ = (μ F).toReal := by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E μ := (inferInstance : VAddInvariantMeasure L.toAddSubgroup E μ)
  exact congr_arg ENNReal.toReal (h.covolume_eq_volume μ)

theorem covolume_ne_zero : covolume L μ ≠ 0 := by
  rw [covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain (Free.chooseBasis ℤ L) μ),
    ENNReal.toReal_ne_zero]
  refine ⟨measure_fundamentalDomain_ne_zero _, ne_of_lt ?_⟩
  exact Bornology.IsBounded.measure_lt_top (fundamentalDomain_isBounded _)

theorem covolume_pos : 0 < covolume L μ :=
  lt_of_le_of_ne ENNReal.toReal_nonneg (covolume_ne_zero L μ).symm

theorem covolume_eq_det_mul_measure {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L)
    (b₀ : Basis ι ℝ E) :
    covolume L μ = |b₀.det ((↑) ∘ b)| * (μ (fundamentalDomain b₀)).toReal := by
  rw [covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain b μ),
    measure_fundamentalDomain _ _ b₀, measure_congr (fundamentalDomain_ae_parallelepiped b₀ μ),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  congr
  ext
  exact b.ofZLatticeBasis_apply ℝ L _

theorem covolume_eq_det {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L) :
    covolume L = |(Matrix.of ((↑) ∘ b)).det| := by
  rw [covolume_eq_measure_fundamentalDomain L volume (isAddFundamentalDomain b volume),
    volume_fundamentalDomain, ENNReal.toReal_ofReal (by positivity)]
  congr
  ext1
  exact b.ofZLatticeBasis_apply ℝ L _

theorem covolume_comap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (ν : Measure F := by volume_tac) [Measure.IsAddHaarMeasure ν]
    {e : E ≃L[ℝ] F} (he : MeasurePreserving e μ ν) :
    covolume (ZLattice.map ℝ L e) ν = covolume L μ := by
  rw [covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain (Free.chooseBasis ℤ L) μ),
    covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain
    ((Free.chooseBasis ℤ L).ofZLatticeMap ℝ L e) ν), ← he.measure_preimage
    (fundamentalDomain_measurableSet _).nullMeasurableSet, ← e.image_symm_eq_preimage,
    ← e.symm.coe_toLinearEquiv, map_fundamentalDomain]
  congr!
  ext i
  simp_rw [ContinuousLinearEquiv.symm_toLinearEquiv, Basis.map_apply, Basis.ofZLatticeBasis_apply,
    Basis.ofZLatticeMap_apply]
  exact e.symm_apply_apply _

theorem volume_image_eq_volume_div_covolume {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L)
    (s : Set (ι → ℝ)) :
    volume ((b.ofZLatticeBasis ℝ L).equivFun '' s) = (volume s) / ENNReal.ofReal (covolume L) := by
  sorry

end Real

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

theorem volume_image_eq_volume_div_covolume' {s : Set E} (hs : MeasurableSet s)
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) :
    volume ((b.ofZLatticeBasis ℝ).equivFun '' s) = volume s / ENNReal.ofReal (covolume L) := by
  sorry

open Bornology Filter Topology

theorem tendsto_card_le_div_covolume' {X : Set E} (hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 < r → r • x ∈ X)
    {F : E → ℝ} (hF₁ : ∀ x ⦃r : ℝ⦄, 0 < r →  F (r • x) = r ^ finrank ℝ E * (F x))
    (hF₂ : IsBounded {x ∈ X | F x ≤ 1}) (hF₃ : MeasurableSet {x ∈ X | F x ≤ 1})
    (hF₄ : volume (frontier {x ∈ X | F x ≤  1}) = 0) [Nontrivial E] :
    Tendsto (fun c : ℝ ↦
      Nat.card ({x ∈ X | F x ≤ c} ∩ L : Set E) / (c : ℝ))
        atTop (𝓝 ((volume {x ∈ X | F x ≤ 1}).toReal / covolume L)) := by
  sorry

end InnerProductSpace

end ZLattice
