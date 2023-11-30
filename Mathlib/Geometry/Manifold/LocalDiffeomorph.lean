/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv

/-!
# Local diffeomorphisms between smooth manifolds

In this file, we define `C^n` local diffeomorphisms between manifolds.

A `C^n` map `f : M → N` is a **local diffeomorphism at `x`** iff there are neighbourhoods `s`
and `t` of `x` and `f x`, respectively such that `f` restricts to a diffeomorphism from `s` and `t`.
`f` is called a **local diffeomorphism** iff it is a local diffeomorphism at every `x ∈ M`.

## Main definitions
* `LocalDiffeomorphAt I J M N n f x`: `f` is a `C^n` local diffeomorphism at `x`
* `LocalDiffeomorph I J M N n f`: `f` is a `C^n` local diffeomorphism

## Main results
* Each of `Diffeomorph`, `LocalDiffeomorph`, and `LocalDiffeomorphAt` implies the next condition.
* `LocalDiffeomorph.isOpen_range`: the image of a local diffeomorphism is open

## TODO
* a local diffeomorphism is a diffeomorphism to its image
* a bijective local diffeomorphism is a diffeomorphism.
* each differential of a `C^n` diffeomorphism (`n ≥ 1`) is a linear equivalence.
* if `f` is a local diffeomorphism at `x`, the differential `mfderiv I J n f x`
is a continuous linear isomorphism.
* conversely, if `f` is `C^n` at `x` and `mfderiv I J n f x` is a linear isomorphism,
`f` is a local diffeomorphism at `x`.
* if `f` is a local diffeomorphism, each differential `mfderiv I J n f x`
is a continuous linear isomorphism.
* Conversely, if `f` is `C^n` and each differential is a linear isomorphism,
`f` is a local diffeomorphism.

## Implementation notes

This notion of diffeomorphism is needed although there is already a notion of local structomorphism
because structomorphisms do not allow the model spaces `H` and `H'` of the two manifolds to be
different, i.e. for a structomorphism one has to impose `H = H'` which is often not the case in
practice.

## Tags
local diffeomorphism, manifold

-/

open Manifold Set  TopologicalSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H]
  {G : Type*} [TopologicalSpace G]
  (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F G)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  (N : Type*) [TopologicalSpace N] [ChartedSpace G N] (n : ℕ∞)

section PartialDiffeomorph
/-- A partial diffeomorphism on `s` is a function `f : M → N` such that `f` restricts to a
diffeomorphism `s → t` between open subsets of `M` and `N`, respectively.
This is an auxiliary definition and should not be used outside of this file. -/
structure PartialDiffeomorph extends LocalHomeomorph M N where
  contMDiffOn_toFun : ContMDiffOn I J n toFun source
  contMDiffOn_invFun : ContMDiffOn J I n invFun target

/-- Coercion of a `PartialDiffeomorph` to function.
Note that a `PartialDiffeomorph` is not `FunLike` (like `LocalHomeomorph`),
as `toFun` doesn't determine `invFun` outside of `target`. -/
instance : CoeFun (PartialDiffeomorph I J M N n) fun _ => M → N :=
  ⟨fun Φ => Φ.toFun'⟩

-- Add the very basic API we need.
namespace PartialDiffeomorph
variable (Φ : PartialDiffeomorph I J M N n) (hn : 1 ≤ n)

/-- The inverse of a local diffeomorphism. -/
protected def symm : PartialDiffeomorph J I N M n := by
  exact {
    toLocalHomeomorph := Φ.toLocalHomeomorph.symm
    contMDiffOn_toFun := Φ.contMDiffOn_invFun
    contMDiffOn_invFun := Φ.contMDiffOn_toFun
  }

protected theorem contMDiffOn : ContMDiffOn I J n Φ Φ.source :=
  Φ.contMDiffOn_toFun

protected theorem contMDiffOn_symm : ContMDiffOn J I n Φ.symm Φ.target :=
  Φ.contMDiffOn_invFun

protected theorem mdifferentiableOn : MDifferentiableOn I J Φ Φ.source :=
  (Φ.contMDiffOn).mdifferentiableOn hn

protected theorem mdifferentiableOn_symm : MDifferentiableOn J I Φ.symm Φ.target :=
  (Φ.symm).mdifferentiableOn hn

protected theorem mdifferentiableAt {x : M} (hx : x ∈ Φ.source) : MDifferentiableAt I J Φ x :=
  (Φ.mdifferentiableOn hn x hx).mdifferentiableAt (Φ.open_source.mem_nhds hx)

protected theorem mdifferentiableAt_symm {x : M} (hx : x ∈ Φ.source) :
    MDifferentiableAt J I Φ.symm (Φ x) :=
  (Φ.symm).mdifferentiableAt hn (Φ.map_source hx)

/- We could add lots of additional API (following `Diffeomorph` and `LocalHomeomorph*), such as
* further continuity and differentiability lemmas
* refl and trans instances; lemmas between them.
As this declaration is meant for internal use only, we keep it simple. -/
end PartialDiffeomorph
end PartialDiffeomorph

variable {M N}

/-- `f : M → N` is called a **`C^n` local diffeomorphism at *x*** iff there exist
  open sets `U ∋ x` and `V ∋ f x` and a diffeomorphism `Φ : U → V` such that `f = Φ` on `U`. -/
def IsLocalDiffeomorphAt (f : M → N) (x : M) : Prop :=
  ∃ Φ : PartialDiffeomorph I J M N n, x ∈ Φ.source ∧ EqOn f Φ Φ.source

/-- `f : M → N` is a **`C^n` local diffeomorphism** iff it is a local diffeomorphism
at each `x ∈ M`. -/
def IsLocalDiffeomorph (f : M → N) : Prop :=
  ∀ x : M, IsLocalDiffeomorphAt I J n f x

lemma isLocalDiffeomorph_iff {f : M → N} :
    IsLocalDiffeomorph I J n f ↔ ∀ x : M, IsLocalDiffeomorphAt I J n f x := by rfl

variable {n}

/-! # Basic properties of local diffeomorphisms -/
section Basic
variable {f : M → N} {x : M}

/-- A `C^n` local diffeomorphism at `x` is `C^n` differentiable at `x`. -/
lemma contMDiffAt_of_isLocalDiffeomorphAt (hf : IsLocalDiffeomorphAt I J n f x) :
    ContMDiffAt I J n f x := by
  choose Φ hx heq using hf
  -- In fact, even `ContMDiffOn I J n f Φ.source`.
  exact ((Φ.contMDiffOn_toFun).congr heq).contMDiffAt (Φ.open_source.mem_nhds hx)

/-- A local diffeomorphism at `x` is differentiable at `x`. -/
lemma mdifferentiableAt_of_isLocalDiffeomorphAt (hn : 1 ≤ n) (hf : IsLocalDiffeomorphAt I J n f x) :
    MDifferentiableAt I J f x :=
  (contMDiffAt_of_isLocalDiffeomorphAt I J hf).mdifferentiableAt hn

/-- A `C^n` local diffeomorphism is `C^n`. -/
lemma contMDiff_of_isLocalDiffeomorph (hf : IsLocalDiffeomorph I J n f) : ContMDiff I J n f :=
  fun x ↦ contMDiffAt_of_isLocalDiffeomorphAt I J (hf x)

/-- A `C^n` local diffeomorphism is differentiable. -/
lemma mdifferentiable_of_isLocalDiffeomorph (hn : 1 ≤ n) (hf : IsLocalDiffeomorph I J n f) :
    MDifferentiable I J f :=
  fun x ↦ mdifferentiableAt_of_isLocalDiffeomorphAt I J hn (hf x)

/-- A diffeomorphism is a partial diffeomorphism. -/
def Diffeomorph.toPartialDiffeomorph (h : Diffeomorph I J M N n) : PartialDiffeomorph I J M N n :=
  {
    toLocalHomeomorph := h.toHomeomorph.toLocalHomeomorph
    contMDiffOn_toFun := fun x _ ↦ h.contMDiff_toFun x
    contMDiffOn_invFun := fun _ _ ↦ h.symm.contMDiffWithinAt
  }

/-- A `C^n` diffeomorphism is a local diffeomorphism. -/
lemma Diffeomorph.isLocalDiffeomorph (Φ : M ≃ₘ^n⟮I, J⟯ N) : IsLocalDiffeomorph I J n Φ :=
  fun _ ↦ ⟨Φ.toPartialDiffeomorph, by trivial, eqOn_refl Φ _⟩

/-- A local diffeomorphism has open range. -/
lemma LocalDiffeomorph.isOpen_range {f : M → N} (hf : IsLocalDiffeomorph I J n f) :
    IsOpen (range f) := by
  apply isOpen_iff_forall_mem_open.mpr
  intro y hy

  -- Given `y = f x ∈ range f`, we need to find `V ⊆ N` open containing `y`.
  rw [mem_range] at hy
  rcases hy with ⟨x, hxy⟩

  -- As f is a local diffeo at x, on some open set `U' ∋ x` it agrees with a diffeo `Φ : U' → V'`.
  choose Φ hyp using hf x
  rcases hyp with ⟨hxU, heq⟩
  -- Then `V:=Φ.target` has the desired properties.
  refine ⟨Φ.target, ?_, Φ.open_target, ?_⟩
  · rw [← LocalHomeomorph.image_source_eq_target, ← heq.image_eq]
    exact image_subset_range f Φ.source
  · rw [← hxy, heq hxU]
    exact Φ.toLocalHomeomorph.map_source hxU

/-- The image of a local diffeomorphism is open. -/
def LocalDiffeomorph.image {f : M → N} (hf : IsLocalDiffeomorph I J n f) : Opens N :=
  ⟨range f, isOpen_range I J hf⟩

lemma LocalDiffeomorph.image_coe {f : M → N} (hf : IsLocalDiffeomorph I J n f) :
    (LocalDiffeomorph.image I J hf).1 = range f := rfl

end Basic
