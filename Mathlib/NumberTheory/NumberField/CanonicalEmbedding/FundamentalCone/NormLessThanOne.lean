/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone.Equiv
import Mathlib.NumberTheory.NumberField.Discriminant
import Mathlib.NumberTheory.NumberField.Units.Regulator

variable (K : Type*) [Field K] [NumberField K]

open Bornology NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units

namespace NumberField.mixedEmbedding.fundamentalCone

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
