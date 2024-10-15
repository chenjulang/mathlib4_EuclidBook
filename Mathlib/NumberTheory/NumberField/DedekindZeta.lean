/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.NumberField.Ideal

import Mathlib.Sandbox

/-!
# Docstring

-/

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

namespace NumberField

open Filter Ideal NumberField.InfinitePlace NumberField.Units Topology

open scoped Real

def dedekindZeta (s : ℂ) :=
    LSeries (fun n ↦ Nat.card {I : Ideal (𝓞 K) // absNorm I = n}) s

def residue : ℝ :=
    (2 ^ NrRealPlaces K * (2 * π) ^ NrComplexPlaces K * regulator K * classNumber K) /
        (torsionOrder K *  Real.sqrt |discr K|)

theorem residue_pos : 0 < residue K := by
  refine div_pos ?_ ?_
  · refine mul_pos ?_ ?_
    · refine mul_pos ?_ ?_
      positivity
      exact regulator_pos K
    · rw [Nat.cast_pos]
      rw [Nat.pos_iff_ne_zero]
      exact classNumber_ne_zero K
  · refine mul_pos ?_ ?_
    · rw [Nat.cast_pos]
      exact PNat.pos (torsionOrder K)
    · refine Real.sqrt_pos_of_pos ?_
      rw [abs_pos]
      rw [Int.cast_ne_zero]
      exact discr_ne_zero K

theorem residue_ne_zero : residue K ≠ 0 := (residue_pos K).ne'

theorem dedekindZeta_residue :
    Tendsto (fun s  : ℝ ↦ (s - 1) * dedekindZeta K s) (𝓝[>] 1) (𝓝 (residue K)) := by
  refine main₂ (residue_pos K) ?_
  dsimp [A]
  convert (ideal.tendsto_norm_le_div_atop K).comp tendsto_natCast_atTop_atTop with n
  simp_rw [Function.comp_apply, Nat.cast_le]
  congr
  have : ∀ i, Fintype {I : Ideal (𝓞 K) | absNorm I = i} := by
    intro i
    refine Set.Finite.fintype ?_
    exact finite_setOf_absNorm_eq i
  have : ∀ i, Fintype {I : Ideal (𝓞 K) | absNorm I ≤ i} := by
    intro i
    refine Set.Finite.fintype ?_
    exact finite_setOf_absNorm_le i
  simp_rw (config := {singlePass := true}) [← Set.coe_setOf, Nat.card_eq_card_toFinset]
  rw [Finset.card_eq_sum_card_fiberwise (t := Finset.range (n + 1)) (f := fun I ↦ absNorm I)]
  · congr! with n hn
    ext
    simp only [Set.mem_toFinset, Set.mem_setOf_eq, Finset.mem_filter, iff_and_self]
    intro h
    rw [h]
    exact Finset.mem_range_succ_iff.mp hn
  · intro x hx
    simp at hx
    exact Finset.mem_range_succ_iff.mpr hx

end NumberField
