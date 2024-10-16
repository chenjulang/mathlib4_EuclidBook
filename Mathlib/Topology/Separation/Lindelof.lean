/-
Copyright (c) 2024 Steven Clontz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Clontz
-/
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Separation

/-!
# Regular Lindelöf spaces

## Main result

* `NormalSpace.of_regularSpace_lindelofSpace`: every regular Lindelöf space is normal.

## References

* [Willard's *General Topology*][zbMATH02107988]

-/

open Set

variable {X : Type*} [TopologicalSpace X]

/-- This technique to witness `HasSeparatingCover` in regular Lindelöf topological spaces
will be used to prove regular Lindelöf spaces are normal. -/
lemma IsClosed.HasSeparatingCover {s t : Set X} [LindelofSpace X] [RegularSpace X]
    (s_cl : IsClosed s) (t_cl : IsClosed t) (st_dis : Disjoint s t) : HasSeparatingCover s t := by
  -- `IsLindelof.indexed_countable_subcover` requires the space be Nonempty
  rcases isEmpty_or_nonempty X with empty_X | nonempty_X
  · rw [subset_eq_empty (t := s) (fun ⦃_⦄ _ ↦ trivial) (univ_eq_empty_iff.mpr empty_X)]
    exact hasSeparatingCovers_iff_separatedNhds.mpr (SeparatedNhds.empty_left t) |>.1
  -- This is almost `HasSeparatingCover`, but is not countable. We define for all `a : X` for use
  -- with `IsLindelof.indexed_countable_subcover` momentarily.
  have (a : X) : ∃ n : Set X, IsOpen n ∧ Disjoint (closure n) t ∧ (a ∈ s → a ∈ n) := by
    wlog ains : a ∈ s
    · exact ⟨∅, isOpen_empty, SeparatedNhds.empty_left t |>.disjoint_closure_left, fun a ↦ ains a⟩
    obtain ⟨n, nna, ncl, nsubkc⟩ := ((regularSpace_TFAE X).out 0 3 :).mp ‹RegularSpace X› a tᶜ <|
      t_cl.compl_mem_nhds (disjoint_left.mp st_dis ains)
    exact
      ⟨interior n,
       isOpen_interior,
       disjoint_left.mpr fun ⦃_⦄ ain ↦
         nsubkc <| (IsClosed.closure_subset_iff ncl).mpr interior_subset ain,
       fun _ ↦ mem_interior_iff_mem_nhds.mpr nna⟩
  -- By Lindelöf, we may obtain a countable subcover witnessing `HasSeparatingCover`
  choose u u_open u_dis u_nhd using this
  obtain ⟨f, f_cov⟩ := s_cl.isLindelof.indexed_countable_subcover
    u u_open (fun a ainh ↦ mem_iUnion.mpr ⟨a, u_nhd a ainh⟩)
  exact ⟨u ∘ f, f_cov, fun n ↦ ⟨u_open (f n), u_dis (f n)⟩⟩

set_option pp.universes true in
/-- A regular topological space with a Lindelöf topology is a normal space. A consequence of e.g.
Corollaries 20.8 and 20.10 of [Willard's *General Topology*][zbMATH02107988] (without the
assumption of Hausdorff). -/
instance (priority := 100) NormalSpace.of_regularSpace_lindelofSpace
    [RegularSpace X] [LindelofSpace X] : NormalSpace X where
  normal _ _ hcl kcl hkdis :=
    hasSeparatingCovers_iff_separatedNhds.mp
    ⟨hcl.HasSeparatingCover kcl hkdis, kcl.HasSeparatingCover hcl (Disjoint.symm hkdis)⟩

instance (priority := 100) NormalSpace.of_regularSpace_secondCountableTopology
    [RegularSpace X] [SecondCountableTopology X] : NormalSpace X :=
  of_regularSpace_lindelofSpace
