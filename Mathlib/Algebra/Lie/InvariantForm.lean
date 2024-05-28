/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Lie algebras with non-degenerate invariant bilinear forms are semisimple

In this file we prove that a finite-dimensional Lie algebra over a field is semisimple
if it does not have non-trivial abelian ideals and it admits a
non-degenerate reflexive invariant bilinear form.
Here a form is *invariant* if it is compatible with the Lie bracket: `Φ ⁅x, y⁆ z = Φ x ⁅y, z⁆`.

## Main results

* `orthogonalLieIdeal`: given a Lie ideal `I`, we define its orthogonal complement with respect to
  a non-degenerate invariant bilinear form `Φ` as the Lie ideal of elements `x` such that
  `Φ n x = 0` for all `n ∈ I`.
* `isSemisimple_of_nondegenerate`: the main result of this file;
  a finite-dimensional Lie algebra over a field is semisimple
  if it does not have non-trivial abelian ideals and admits
  a non-degenerate invariant reflexive bilinear form.

## References

We follow the short and excellent paper [dieudonne1953].
-/

namespace LieAlgebra

namespace InvariantForm

section ring

variable {R L M : Type*}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable (Φ : LinearMap.BilinForm R L) (hΦ_nondeg : Φ.Nondegenerate)
variable (hΦ_inv : ∀ x y z, Φ ⁅x, y⁆ z = Φ x ⁅y, z⁆)
variable (hL : ∀ I : LieIdeal R L, IsAtom I → ¬IsLieAbelian I)

/--
The orthogonal complement of a Lie ideal `I` with respect to an invariant bilinear form `Φ` is
the Lie ideal of elements `y` such that `Φ x y = 0` for all `x ∈ I`.
-/
@[simps!]
def orthogonalLieIdeal (I : LieIdeal R L) : LieIdeal R L where
  __ := Φ.orthogonal I
  lie_mem {x y} := by
    suffices (∀ n ∈ I, Φ n y = 0) → ∀ n ∈ I, Φ n ⁅x, y⁆ = 0 by
      simpa only [LinearMap.BilinForm.isOrtho_def, -- and some default simp lemmas
        LieIdeal.coe_to_lieSubalgebra_to_submodule, AddSubsemigroup.mem_carrier,
        AddSubmonoid.mem_toSubsemigroup, Submodule.mem_toAddSubmonoid,
        LinearMap.BilinForm.mem_orthogonal_iff, LieSubmodule.mem_coeSubmodule]
    intro H a ha
    rw [← hΦ_inv]
    apply H
    apply lie_mem_left
    apply ha

@[simp]
lemma orthogonalLieIdeal_toSubmodule (I : LieIdeal R L) :
    (orthogonalLieIdeal Φ hΦ_inv I).toSubmodule = Φ.orthogonal I.toSubmodule := rfl

lemma mem_orthogonalLieIdeal (I : LieIdeal R L) (y : L) :
    y ∈ orthogonalLieIdeal Φ hΦ_inv I ↔ ∀ x ∈ I, Φ x y = 0 := by
  simp [orthogonalLieIdeal, LinearMap.BilinForm.isOrtho_def, LinearMap.BilinForm.mem_orthogonal_iff]

lemma orthogonalLieIdeal_disjoint (I : LieIdeal R L) (hI : IsAtom I) :
    Disjoint I (orthogonalLieIdeal  Φ hΦ_inv I) := by
  rw [disjoint_iff, ← hI.lt_iff, lt_iff_le_and_ne]
  suffices ¬I ≤ orthogonalLieIdeal Φ hΦ_inv I by
    simpa only [inf_le_left, ne_eq, inf_eq_left, true_and]
  intro contra
  apply hI.1
  rw [eq_bot_iff, ← perfect_of_isAtom_of_nonabelian I hI (hL I hI),
      LieSubmodule.lieIdeal_oper_eq_span, LieSubmodule.lieSpan_le]
  rintro _ ⟨x, y, rfl⟩
  simp only [LieSubmodule.bot_coe, Set.mem_singleton_iff]
  apply hΦ_nondeg
  intro z
  rw [hΦ_inv]
  have hyz : ⁅(y : L), z⁆ ∈ I := lie_mem_left _ _ _ _ _ y.2
  exact contra hyz x x.2

end ring

section field

variable {K L M : Type*}
variable [Field K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M]

variable [Module.Finite K L]
variable (Φ : LinearMap.BilinForm K L) (hΦ_nondeg : Φ.Nondegenerate)
variable (hΦ_inv : ∀ x y z, Φ ⁅x, y⁆ z = Φ x ⁅y, z⁆) (hΦ_refl : Φ.IsRefl)
variable (hL : ∀ I : LieIdeal K L, IsAtom I → ¬IsLieAbelian I)

open FiniteDimensional Submodule in
lemma orthogonalLieIdeal_isCompl_submodule (I : LieIdeal K L) (hI : IsAtom I) :
    IsCompl I.toSubmodule (orthogonalLieIdeal Φ hΦ_inv I).toSubmodule := by
  have := (orthogonalLieIdeal_disjoint Φ hΦ_nondeg hΦ_inv hL I hI).eq_bot
  apply_fun LieSubmodule.toSubmodule at this
  simp only [LieSubmodule.inf_coe_toSubmodule, LieSubmodule.bot_coeSubmodule,
    orthogonalLieIdeal_toSubmodule] at this ⊢
  refine IsCompl.of_eq this ?_
  apply (eq_top_of_finrank_eq <| (finrank_le _).antisymm _)
  conv_rhs => rw [← add_zero (finrank K _)]
  rw [← finrank_bot K L, ← this, finrank_sup_add_finrank_inf_eq]
  erw [LinearMap.BilinForm.finrank_add_finrank_orthogonal hΦ_refl (W := I)]
  exact le_self_add

open FiniteDimensional Submodule in
lemma orthogonalLieIdeal_isCompl (I : LieIdeal K L) (hI : IsAtom I) :
    IsCompl I (orthogonalLieIdeal Φ hΦ_inv I) := by
  have := orthogonalLieIdeal_isCompl_submodule Φ hΦ_nondeg hΦ_inv hΦ_refl hL I hI
  apply IsCompl.of_eq
  · rw [eq_bot_iff]
    exact this.disjoint.le_bot
  · rw [eq_top_iff]
    exact this.codisjoint.top_le

lemma restrict_nondegenerate (I : LieIdeal K L) (hI : IsAtom I) :
    (Φ.restrict I).Nondegenerate := by
  rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hΦ_refl]
  exact orthogonalLieIdeal_isCompl_submodule Φ hΦ_nondeg hΦ_inv hΦ_refl hL I hI

lemma restrict_orthogonal_nondegenerate (I : LieIdeal K L) (hI : IsAtom I) :
    (Φ.restrict (orthogonalLieIdeal Φ hΦ_inv I)).Nondegenerate := by
  rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hΦ_refl]
  simp only [LieIdeal.coe_to_lieSubalgebra_to_submodule, orthogonalLieIdeal_toSubmodule,
    LinearMap.BilinForm.orthogonal_orthogonal hΦ_nondeg hΦ_refl]
  exact (orthogonalLieIdeal_isCompl_submodule Φ hΦ_nondeg hΦ_inv hΦ_refl hL I hI).symm

open FiniteDimensional Submodule in
lemma atomistic : ∀ I : LieIdeal K L, sSup {J : LieIdeal K L | IsAtom J ∧ J ≤ I} = I := by
  intro I
  apply le_antisymm
  · apply sSup_le
    rintro J ⟨-, hJ'⟩
    exact hJ'
  by_cases hI : I = ⊥
  · exact hI.le.trans bot_le
  obtain ⟨J, hJ, hJI⟩ := LieSubmodule.exists_atom_le_of_finite I hI
  let J' := orthogonalLieIdeal Φ hΦ_inv J
  suffices I ≤ J ⊔ (J' ⊓ I) by
    refine this.trans ?_
    apply sup_le
    · exact le_sSup ⟨hJ, hJI⟩
    rw [← atomistic (J' ⊓ I)]
    apply sSup_le_sSup
    simp only [le_inf_iff, Set.setOf_subset_setOf, and_imp]
    tauto
  suffices J ⊔ J' = ⊤ by rw [← sup_inf_assoc_of_le _ hJI, this, top_inf_eq]
  exact (orthogonalLieIdeal_isCompl Φ hΦ_nondeg hΦ_inv hΦ_refl hL J hJ).codisjoint.eq_top
termination_by I => finrank K I
decreasing_by
  apply finrank_lt_finrank_of_lt
  suffices ¬I ≤ J' by simpa
  intro hIJ'
  apply hJ.1
  rw [eq_bot_iff]
  exact orthogonalLieIdeal_disjoint Φ hΦ_nondeg hΦ_inv hL J hJ le_rfl (hJI.trans hIJ')

open LieSubmodule in
/--
A finite-dimensional Lie algebra over a field is semisimple
if it does not have non-trivial abelian ideals and it admits a
non-degenerate reflexive invariant bilinear form.
Here a form is *invariant* if it is compatible with the Lie bracket: `Φ ⁅x, y⁆ z = Φ x ⁅y, z⁆`.
-/
theorem isSemisimple_of_nondegenerate : IsSemisimple K L := by
  refine ⟨?_, ?_, hL⟩
  · simpa using atomistic Φ hΦ_nondeg hΦ_inv hΦ_refl hL ⊤
  intro I hI
  apply (orthogonalLieIdeal_disjoint Φ hΦ_nondeg hΦ_inv hL I hI).mono_right
  apply sSup_le
  simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff, and_imp]
  intro J hJ hJI
  rw [← perfect_of_isAtom_of_nonabelian J hJ (hL J hJ), lieIdeal_oper_eq_span, lieSpan_le]
  rintro _ ⟨x, y, rfl⟩
  simp only [orthogonalLieIdeal_carrier, Φ.isOrtho_def, Set.mem_setOf_eq]
  intro z hz
  rw [← hΦ_inv]
  suffices ⁅z, (x : L)⁆ = 0 by simp only [this, map_zero, LinearMap.zero_apply]
  rw [← LieSubmodule.mem_bot (R := K) (L := L), ← (hJ.disjoint_of_ne hI hJI).symm.eq_bot]
  apply lie_le_inf
  exact lie_mem_lie _ _ hz x.2

end field

end InvariantForm

end LieAlgebra
