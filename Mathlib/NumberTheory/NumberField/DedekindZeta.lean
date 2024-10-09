/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.NumberField.Ideal

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

theorem dedekindZeta_residue :
    Tendsto (fun s  : ℝ ↦ (s - 1) * dedekindZeta K s) (𝓝[<] 1) (𝓝 (residue K)) := sorry

end NumberField
