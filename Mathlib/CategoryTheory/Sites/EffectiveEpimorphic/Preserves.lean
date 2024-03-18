/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic.Basic
/-!

# Functors preserving effective epimorphisms

This file concerns functors which preserve effective epimorphisms and effective epimporphic
families.

## TODO
- Find sufficient conditions on functors to preserve/reflect effective epis.
-/

universe u

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C]

noncomputable section Equivalence

variable {D : Type*} [Category D] (e : C ≌ D) {B : C}

variable {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B)) [EffectiveEpiFamily X π]

theorem effectiveEpiFamilyStructOfEquivalence_aux {W : D} (ε : (a : α) → e.functor.obj (X a) ⟶ W)
    (h : ∀ {Z : D} (a₁ a₂ : α) (g₁ : Z ⟶ e.functor.obj (X a₁)) (g₂ : Z ⟶ e.functor.obj (X a₂)),
      g₁ ≫ e.functor.map (π a₁) = g₂ ≫ e.functor.map (π a₂) → g₁ ≫ ε a₁ = g₂ ≫ ε a₂)
    {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂) (hg : g₁ ≫ π a₁ = g₂ ≫ π a₂) :
    g₁ ≫ (fun a ↦ e.unit.app (X a) ≫ e.inverse.map (ε a)) a₁ =
    g₂ ≫ (fun a ↦ e.unit.app (X a) ≫ e.inverse.map (ε a)) a₂ := by
  have := h a₁ a₂ (e.functor.map g₁) (e.functor.map g₂)
  simp only [← Functor.map_comp, hg] at this
  simpa using congrArg e.inverse.map (this (by trivial))

/-- Equivalences preserve effective epimorphic families -/
def effectiveEpiFamilyStructOfEquivalence : EffectiveEpiFamilyStruct (fun a ↦ e.functor.obj (X a))
    (fun a ↦ e.functor.map (π a)) where
  desc ε h := (e.toAdjunction.homEquiv _ _).symm
      (EffectiveEpiFamily.desc X π (fun a ↦ e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h))
  fac ε h a := by
    simp only [Functor.comp_obj, Adjunction.homEquiv_counit, Functor.id_obj,
      Equivalence.toAdjunction_counit]
    have := congrArg ((fun f ↦ f ≫ e.counit.app _) ∘ e.functor.map)
      (EffectiveEpiFamily.fac X π (fun a ↦ e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h) a)
    simp only [Functor.id_obj, Functor.comp_obj, Function.comp_apply, Functor.map_comp,
        Category.assoc, Equivalence.fun_inv_map, Iso.inv_hom_id_app, Category.comp_id] at this
    simp [this]
  uniq ε h m hm := by
    simp only [Functor.comp_obj, Adjunction.homEquiv_counit, Functor.id_obj,
      Equivalence.toAdjunction_counit]
    have := EffectiveEpiFamily.uniq X π (fun a ↦ e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h)
    specialize this (e.unit.app _ ≫ e.inverse.map m) fun a ↦ ?_
    · rw [← congrArg e.inverse.map (hm a)]
      simp
    · simp [← this]

instance (F : C ⥤ D) [IsEquivalence F] :
    EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a ↦ F.map (π a)) :=
  ⟨⟨effectiveEpiFamilyStructOfEquivalence F.asEquivalence _ _⟩⟩

example {X B : C} (π : X ⟶ B) (F : C ⥤ D) [IsEquivalence F] [EffectiveEpi π] :
    EffectiveEpi <| F.map π := inferInstance

end Equivalence

namespace Functor

variable {D : Type*} [Category D]

section Preserves

/--
A functor preserves effective epimorphisms if it maps effective epimorphisms to effective
epimorphisms.
-/
class PreservesEffectiveEpis (F : C ⥤ D) : Prop where
  /--
  A functor preserves effective epimorphisms if it maps effective
  epimorphisms to effective epimorphisms.
  -/
  preserves : ∀ {X Y : C} (f : X ⟶ Y) [EffectiveEpi f], EffectiveEpi (F.map f)

instance map_effectiveEpi (F : C ⥤ D) [F.PreservesEffectiveEpis] {X Y : C} (f : X ⟶ Y)
    [EffectiveEpi f] : EffectiveEpi (F.map f) :=
  PreservesEffectiveEpis.preserves f

/--
A functor preserves effective epimorphic families if it maps effective epimorphic families to
effective epimorphic families.
-/
class PreservesEffectiveEpiFamilies (F : C ⥤ D) : Prop where
  /--
  A functor preserves effective epimorphic families if it maps effective epimorphic families to
  effective epimorphic families.
  -/
  preserves : ∀ {α : Type*} {B : C} (X : α → C) (π : (a : α) → (X a ⟶ B)) [EffectiveEpiFamily X π],
    EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a  ↦ F.map (π a))

instance map_effectiveEpiFamily (F : C ⥤ D) [F.PreservesEffectiveEpiFamilies]
    {α : Type*} {B : C} (X : α → C) (π : (a : α) → (X a ⟶ B)) [EffectiveEpiFamily X π] :
    EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a  ↦ F.map (π a)) :=
  PreservesEffectiveEpiFamilies.preserves X π

instance (F : C ⥤ D) [PreservesEffectiveEpiFamilies F] : PreservesEffectiveEpis F where
  preserves _ := inferInstance

instance (F : C ⥤ D) [IsEquivalence F] : F.PreservesEffectiveEpiFamilies where
  preserves _ _ := inferInstance

end Preserves

section Reflects

/--
A functor reflects effective epimorphisms if it only maps effective epimorphisms to effective
epimorphisms.
-/
class ReflectsEffectiveEpis (F : C ⥤ D) : Prop where
  /--
  A functor reflects effective epimorphisms if it only maps effective
  epimorphisms to effective epimorphisms.
  -/
  reflects : ∀ {X Y : C} (f : X ⟶ Y) [EffectiveEpi (F.map f)], EffectiveEpi f

lemma effectiveEpi_of_map (F : C ⥤ D) [F.ReflectsEffectiveEpis] {X Y : C} (f : X ⟶ Y)
    [EffectiveEpi (F.map f)] : EffectiveEpi f :=
  ReflectsEffectiveEpis.reflects F f

/--
A functor reflects effective epimorphic families if it only maps effective epimorphic families to
effective epimorphic families.
-/
class ReflectsEffectiveEpiFamilies (F : C ⥤ D) : Prop where
  /--
  A functor reflects effective epimorphic families if it only maps effective epimorphic families to
  effective epimorphic families.
  -/
  reflects : ∀ {α : Type u} {B : C} (X : α → C) (π : (a : α) → (X a ⟶ B))
    [EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a  ↦ F.map (π a))],
    EffectiveEpiFamily X π

lemma effectiveEpiFamily_of_map (F : C ⥤ D) [ReflectsEffectiveEpiFamilies.{_, _, u} F]
    {α : Type u} {B : C} (X : α → C) (π : (a : α) → (X a ⟶ B))
    [EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a  ↦ F.map (π a))] :
    EffectiveEpiFamily X π :=
  ReflectsEffectiveEpiFamilies.reflects F X π

instance (F : C ⥤ D) [PreservesEffectiveEpiFamilies F] : PreservesEffectiveEpis F where
  preserves _ := inferInstance

instance (F : C ⥤ D) [IsEquivalence F] : F.PreservesEffectiveEpiFamilies where
  preserves _ _ := inferInstance

end Reflects

end Functor
