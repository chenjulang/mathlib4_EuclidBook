import Mathlib.Data.Set.Basic

variable {α : Type*} (s t : Set α)

example (h : s ≠ t) : ∃ x, (x ∈ s ∧ x ∉ t) ∨ (x ∈ t ∧ x ∉ s) := by
--  rw [← Set.symmDiff_nonempty] at h
  exact Set.symmDiff_nonempty.mpr h

