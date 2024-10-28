/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.AffineAnd
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.RingHom.Finite

/-!

# Finite morphisms of schemes

A morphism of schemes `f : X ⟶ Y` is finite if the preimage
of an arbitrary affine open subset of `Y` is affine and the induced ring map is finite.

It is equivalent to ask only that `Y` is covered by affine opens whose preimage is affine
and the induced ring map is finite.

## TODO

- Show finite morphisms are proper

-/

universe v u

open CategoryTheory TopologicalSpace Opposite MorphismProperty

namespace AlgebraicGeometry

/-- A morphism of schemes `X ⟶ Y` is finite if
the preimage of any affine open subset of `Y` is affine and the induced ring
hom is finite. -/
@[mk_iff]
class IsFinite {X Y : Scheme} (f : X ⟶ Y) extends IsAffineHom f : Prop where
  finite_app (U : Y.affineOpens) : (f.app U).Finite

namespace IsFinite

instance : HasAffineProperty @IsFinite (affineAnd RingHom.Finite) := by
  rw [HasAffineProperty.affineAnd_iff _ RingHom.finite_respectsIso
    RingHom.finite_localizationPreserves RingHom.finite_ofLocalizationSpan]
  simp [isFinite_iff]

instance : IsStableUnderComposition @IsFinite :=
  HasAffineProperty.affineAnd_isStableUnderComposition RingHom.finite_stableUnderComposition

lemma stableUnderBaseChange : StableUnderBaseChange @IsFinite :=
  HasAffineProperty.affineAnd_stableUnderBaseChange
    RingHom.finite_respectsIso RingHom.finite_stableUnderBaseChange

instance : ContainsIdentities @IsFinite :=
  HasAffineProperty.affineAnd_containsIdentities RingHom.finite_respectsIso
    RingHom.finite_containsIdentities

instance : IsMultiplicative @IsFinite where

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

instance (priority := 900) [IsIso f] : IsFinite f := of_isIso @IsFinite f

instance (priority := 900) [hf : IsFinite f] : LocallyOfFiniteType f := by
  wlog hY : IsAffine Y
  · rw [IsLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFiniteType) _
      (iSup_affineOpens_eq_top _)]
    intro U
    haveI hfU : IsFinite (f ∣_ U) := IsLocalAtTarget.restrict hf U
    apply this _ U.2
  rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)] at hf
  obtain ⟨hX, hf⟩ := hf
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)]
  exact RingHom.FiniteType.of_finite hf

end IsFinite

end AlgebraicGeometry
