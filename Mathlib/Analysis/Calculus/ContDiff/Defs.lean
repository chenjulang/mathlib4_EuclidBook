/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Analytic.Within
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.HasFTaylorSeries

/-!
# Higher differentiability

A function is `C^1` on a domain if it is differentiable there, and its derivative is continuous.
By induction, it is `C^n` if it is `C^{n-1}` and its (n-1)-th derivative is `C^1` there or,
equivalently, if it is `C^1` and its derivative is `C^{n-1}`.
It is `C^∞` if it is `C^n` for all n.
Finally, it is `C^ω` if it is analytic (as well as all its derivative, which is automatic if the
space is complete).

We formalize these notions by defining iteratively the `n+1`-th derivative of a function as the
derivative of the `n`-th derivative. It is called `iteratedFDeriv 𝕜 n f x` where `𝕜` is the
field, `n` is the number of iterations, `f` is the function and `x` is the point, and it is given
as an `n`-multilinear map. We also define a version `iteratedFDerivWithin` relative to a domain,
as well as predicates `ContDiffWithinAt`, `ContDiffAt`, `ContDiffOn` and
`ContDiff` saying that the function is `C^n` within a set at a point, at a point, on a set
and on the whole space respectively.

To avoid the issue of choice when choosing a derivative in sets where the derivative is not
necessarily unique, `ContDiffOn` is not defined directly in terms of the
regularity of the specific choice `iteratedFDerivWithin 𝕜 n f s` inside `s`, but in terms of the
existence of a nice sequence of derivatives, expressed with a predicate
`HasFTaylorSeriesUpToOn`.

We prove basic properties of these notions.

## Main definitions and results
Let `f : E → F` be a map between normed vector spaces over a nontrivially normed field `𝕜`.

* `HasFTaylorSeriesUpTo n f p`: expresses that the formal multilinear series `p` is a sequence
  of iterated derivatives of `f`, up to the `n`-th term (where `n` is a natural number or `∞`).
* `HasFTaylorSeriesUpToOn n f p s`: same thing, but inside a set `s`. The notion of derivative
  is now taken inside `s`. In particular, derivatives don't have to be unique.
* `ContDiff 𝕜 n f`: expresses that `f` is `C^n`, i.e., it admits a Taylor series up to
  rank `n`.
* `ContDiffOn 𝕜 n f s`: expresses that `f` is `C^n` in `s`.
* `ContDiffAt 𝕜 n f x`: expresses that `f` is `C^n` around `x`.
* `ContDiffWithinAt 𝕜 n f s x`: expresses that `f` is `C^n` around `x` within the set `s`.
* `iteratedFDerivWithin 𝕜 n f s x` is an `n`-th derivative of `f` over the field `𝕜` on the
  set `s` at the point `x`. It is a continuous multilinear map from `E^n` to `F`, defined as a
  derivative within `s` of `iteratedFDerivWithin 𝕜 (n-1) f s` if one exists, and `0` otherwise.
* `iteratedFDeriv 𝕜 n f x` is the `n`-th derivative of `f` over the field `𝕜` at the point `x`.
  It is a continuous multilinear map from `E^n` to `F`, defined as a derivative of
  `iteratedFDeriv 𝕜 (n-1) f` if one exists, and `0` otherwise.

In sets of unique differentiability, `ContDiffOn 𝕜 n f s` can be expressed in terms of the
properties of `iteratedFDerivWithin 𝕜 m f s` for `m ≤ n`. In the whole space,
`ContDiff 𝕜 n f` can be expressed in terms of the properties of `iteratedFDeriv 𝕜 m f`
for `m ≤ n`.

## Implementation notes

The definitions in this file are designed to work on any field `𝕜`. They are sometimes slightly more
complicated than the naive definitions one would guess from the intuition over the real or complex
numbers, but they are designed to circumvent the lack of gluing properties and partitions of unity
in general. In the usual situations, they coincide with the usual definitions.

### Definition of `C^n` functions in domains

One could define `C^n` functions in a domain `s` by fixing an arbitrary choice of derivatives (this
is what we do with `iteratedFDerivWithin`) and requiring that all these derivatives up to `n` are
continuous. If the derivative is not unique, this could lead to strange behavior like two `C^n`
functions `f` and `g` on `s` whose sum is not `C^n`. A better definition is thus to say that a
function is `C^n` inside `s` if it admits a sequence of derivatives up to `n` inside `s`.

This definition still has the problem that a function which is locally `C^n` would not need to
be `C^n`, as different choices of sequences of derivatives around different points might possibly
not be glued together to give a globally defined sequence of derivatives. (Note that this issue
can not happen over reals, thanks to partition of unity, but the behavior over a general field is
not so clear, and we want a definition for general fields). Also, there are locality
problems for the order parameter: one could image a function which, for each `n`, has a nice
sequence of derivatives up to order `n`, but they do not coincide for varying `n` and can therefore
not be glued to give rise to an infinite sequence of derivatives. This would give a function
which is `C^n` for all `n`, but not `C^∞`. We solve this issue by putting locality conditions
in space and order in our definition of `ContDiffWithinAt` and `ContDiffOn`.
The resulting definition is slightly more complicated to work with (in fact not so much), but it
gives rise to completely satisfactory theorems.

For instance, with this definition, a real function which is `C^m` (but not better) on `(-1/m, 1/m)`
for each natural `m` is by definition `C^∞` at `0`.

There is another issue with the definition of `ContDiffWithinAt 𝕜 n f s x`. We can
require the existence and good behavior of derivatives up to order `n` on a neighborhood of `x`
within `s`. However, this does not imply continuity or differentiability within `s` of the function
at `x` when `x` does not belong to `s`. Therefore, we require such existence and good behavior on
a neighborhood of `x` within `s ∪ {x}` (which appears as `insert x s` in this file).

### Side of the composition, and universe issues

With a naïve direct definition, the `n`-th derivative of a function belongs to the space
`E →L[𝕜] (E →L[𝕜] (E ... F)...)))` where there are n iterations of `E →L[𝕜]`. This space
may also be seen as the space of continuous multilinear functions on `n` copies of `E` with
values in `F`, by uncurrying. This is the point of view that is usually adopted in textbooks,
and that we also use. This means that the definition and the first proofs are slightly involved,
as one has to keep track of the uncurrying operation. The uncurrying can be done from the
left or from the right, amounting to defining the `n+1`-th derivative either as the derivative of
the `n`-th derivative, or as the `n`-th derivative of the derivative.
For proofs, it would be more convenient to use the latter approach (from the right),
as it means to prove things at the `n+1`-th step we only need to understand well enough the
derivative in `E →L[𝕜] F` (contrary to the approach from the left, where one would need to know
enough on the `n`-th derivative to deduce things on the `n+1`-th derivative).

However, the definition from the right leads to a universe polymorphism problem: if we define
`iteratedFDeriv 𝕜 (n + 1) f x = iteratedFDeriv 𝕜 n (fderiv 𝕜 f) x` by induction, we need to
generalize over all spaces (as `f` and `fderiv 𝕜 f` don't take values in the same space). It is
only possible to generalize over all spaces in some fixed universe in an inductive definition.
For `f : E → F`, then `fderiv 𝕜 f` is a map `E → (E →L[𝕜] F)`. Therefore, the definition will only
work if `F` and `E →L[𝕜] F` are in the same universe.

This issue does not appear with the definition from the left, where one does not need to generalize
over all spaces. Therefore, we use the definition from the left. This means some proofs later on
become a little bit more complicated: to prove that a function is `C^n`, the most efficient approach
is to exhibit a formula for its `n`-th derivative and prove it is continuous (contrary to the
inductive approach where one would prove smoothness statements without giving a formula for the
derivative). In the end, this approach is still satisfactory as it is good to have formulas for the
iterated derivatives in various constructions.

One point where we depart from this explicit approach is in the proof of smoothness of a
composition: there is a formula for the `n`-th derivative of a composition (Faà di Bruno's formula),
but it is very complicated and barely usable, while the inductive proof is very simple. Thus, we
give the inductive proof. As explained above, it works by generalizing over the target space, hence
it only works well if all spaces belong to the same universe. To get the general version, we lift
things to a common universe using a trick.

### Variables management

The textbook definitions and proofs use various identifications and abuse of notations, for instance
when saying that the natural space in which the derivative lives, i.e.,
`E →L[𝕜] (E →L[𝕜] ( ... →L[𝕜] F))`, is the same as a space of multilinear maps. When doing things
formally, we need to provide explicit maps for these identifications, and chase some diagrams to see
everything is compatible with the identifications. In particular, one needs to check that taking the
derivative and then doing the identification, or first doing the identification and then taking the
derivative, gives the same result. The key point for this is that taking the derivative commutes
with continuous linear equivalences. Therefore, we need to implement all our identifications with
continuous linear equivs.

## Notations

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

In this file, we denote `⊤ : ℕ∞` with `∞`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

noncomputable section

open scoped Classical
open NNReal Topology Filter

-- local notation "∞" => (⊤ : ℕ∞)

/-
Porting note: These lines are not required in Mathlib4.
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule' AddCommGroup.toAddCommMonoid
-/

open Set Fin Filter Function

universe u uE uF uG uX

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type uE} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type uG}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {s s₁ t u : Set E} {f f₁ : E → F} {g : F → G} {x x₀ : E} {c : F}
  {p : E → FormalMultilinearSeries 𝕜 E F}


/-! ### Smooth functions within a set around a point -/

local notation "ω" => (⊤ : WithTop (ℕ∞))
local notation "∞" => ((⊤ : ℕ∞) : WithTop (ℕ∞))


variable (𝕜)

variable {m n : WithTop (ℕ∞)}

/-- A function is continuously differentiable up to order `n` within a set `s` at a point `x` if
it admits continuous derivatives up to order `n` in a neighborhood of `x` in `s ∪ {x}`.
For `n = ∞`, we only require that this holds up to any finite order (where the neighborhood may
depend on the finite order we consider).
For `n = ω`, we require the function to be analytic within `s` at `x`. The precise definition we
give is more involved to work around issues when the space is not complete, but it is equivalent
when the space is complete.

For instance, a real function which is `C^m` on `(-1/m, 1/m)` for each natural `m`, but not
better, is `C^∞` at `0` within `univ`.
-/
def ContDiffWithinAt (n : WithTop ℕ∞) (f : E → F) (s : Set E) (x : E) : Prop :=
  match n with
  | ω => ∀ m : ℕ, ∃ u ∈ 𝓝[insert x s] x, ∃ p : E → FormalMultilinearSeries 𝕜 E F,
      HasFTaylorSeriesUpToOn m f p u ∧ ∀ i ≤ m, AnalyticWithinOn 𝕜 (fun x ↦ p x i) u
  | (n : ℕ∞) => ∀ m : ℕ, (m : ℕ∞) ≤ n → ∃ u ∈ 𝓝[insert x s] x,
      ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpToOn m f p u

/-- An auxiliary definition, splitting out a part of the definition of `C^ω` functions.
Implementation detail, not for use outside of the API development for `C^ω` functions. -/
def ContDiffWithinAtOmegaAux (m : ℕ) (f : E → F) (s : Set E) (x : E) : Prop :=
  ∃ u ∈ 𝓝[insert x s] x, ∃ p : E → FormalMultilinearSeries 𝕜 E F,
      HasFTaylorSeriesUpToOn m f p u ∧ ∀ i ≤ m, AnalyticWithinOn 𝕜 (fun x ↦ p x i) u

variable {𝕜}

lemma ContDiffWithinAt.contDiffWithinAtOmegaAux (h : ContDiffWithinAt 𝕜 ω f s x) (n : ℕ) :
    ContDiffWithinAtOmegaAux 𝕜 n f s x := h n

lemma ContDiffWithinAtOmegaAux.analyticWithinOn (h : ContDiffWithinAtOmegaAux 𝕜 0 f s x) :
    ∃ u ∈ 𝓝[insert x s] x, AnalyticWithinOn 𝕜 f u := by
  rcases h with ⟨u, hu, p, hp, h'p⟩
  refine ⟨insert x s ∩ u, inter_mem self_mem_nhdsWithin hu, ?_⟩
  have : AnalyticWithinOn 𝕜 (fun x ↦ (continuousMultilinearCurryFin0 𝕜 E F) (p x 0))
      (insert x s ∩ u) :=
    (LinearIsometryEquiv.analyticOn _ _ ).comp_analyticWithinOn
      ((h'p 0 le_rfl).mono inter_subset_right) (Set.mapsTo_univ _ _)
  exact this.congr (fun y hy ↦ (hp.zero_eq _ hy.2).symm)

lemma ContDiffWithinAtOmegaAux.analyticWithinAt (h : ContDiffWithinAtOmegaAux 𝕜 0 f s x) :
    AnalyticWithinAt 𝕜 f s x := by
  obtain ⟨u, hu, hf⟩ := h.analyticWithinOn
  have xu : x ∈ u := mem_of_mem_nhdsWithin (by simp) hu
  exact (hf x xu).mono_of_mem (nhdsWithin_mono _ (subset_insert _ _) hu)

lemma ContDiffWithinAt.analyticWithinOn (h : ContDiffWithinAt 𝕜 ω f s x) :
    ∃ u ∈ 𝓝[insert x s] x, AnalyticWithinOn 𝕜 f u :=
  (h.contDiffWithinAtOmegaAux 0).analyticWithinOn

lemma ContDiffWithinAt.analyticWithinAt (h : ContDiffWithinAt 𝕜 ω f s x) :
    AnalyticWithinAt 𝕜 f s x :=
  (h.contDiffWithinAtOmegaAux 0).analyticWithinAt

theorem contDiffWithinAt_omega_iff_analyticWithinAt [CompleteSpace F] :
    ContDiffWithinAt 𝕜 ω f s x ↔ AnalyticWithinAt 𝕜 f s x := by
  refine ⟨fun h ↦ h.analyticWithinAt, fun h m ↦ ?_⟩
  obtain ⟨u, hu, p, hp, h'p⟩ := h.exists_hasFTaylorSeriesUpToOn ⊤
  exact ⟨u, hu, p, hp.of_le le_top, fun i _ ↦ h'p i⟩

theorem contDiffWithinAt_nat {n : ℕ} :
    ContDiffWithinAt 𝕜 n f s x ↔ ∃ u ∈ 𝓝[insert x s] x,
      ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpToOn n f p u :=
  ⟨fun H => H n le_rfl, fun ⟨u, hu, p, hp⟩ _m hm => ⟨u, hu, p, hp.of_le hm⟩⟩

theorem ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n f s x) (hmn : m ≤ n) :
    ContDiffWithinAt 𝕜 m f s x := by
  match n with
  | ω => match m with
    | ω => exact h
    | (m : ℕ∞) =>
      intro k _
      rcases h k with ⟨u, hu, p, hp⟩
      exact ⟨u, hu, p, hp.1⟩
  | (n : ℕ∞) => match m with
    | ω => simp at hmn
    | (m : ℕ∞) => exact fun k hk ↦ h k (le_trans hk (by exact_mod_cast hmn))

theorem AnalyticWithinAt.contDiffWithinAt [CompleteSpace F] (h : AnalyticWithinAt 𝕜 f s x) :
    ContDiffWithinAt 𝕜 n f s x :=
  (contDiffWithinAt_omega_iff_analyticWithinAt.2 h).of_le le_top

theorem contDiffWithinAt_iff_forall_nat_le {n : ℕ∞} :
    ContDiffWithinAt 𝕜 n f s x ↔ ∀ m : ℕ, ↑m ≤ n → ContDiffWithinAt 𝕜 m f s x :=
  ⟨fun H m hm => H.of_le (by exact_mod_cast hm), fun H m hm => H m hm _ le_rfl⟩

theorem contDiffWithinAt_top : ContDiffWithinAt 𝕜 ∞ f s x ↔ ∀ n : ℕ, ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAt_iff_forall_nat_le.trans <| by simp only [forall_prop_of_true, le_top]

theorem ContDiffWithinAt.continuousWithinAt (h : ContDiffWithinAt 𝕜 n f s x) :
    ContinuousWithinAt f s x := by
  have := h.of_le (zero_le _)
  simp only [ContDiffWithinAt, nonpos_iff_eq_zero, Nat.cast_eq_zero,
    mem_pure, forall_eq, CharP.cast_eq_zero] at this
  rcases this with ⟨u, hu, p, H⟩
  rw [mem_nhdsWithin_insert] at hu
  exact (H.continuousOn.continuousWithinAt hu.1).mono_of_mem hu.2

theorem ContDiffWithinAt.congr_of_eventuallyEq (h : ContDiffWithinAt 𝕜 n f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 n f₁ s x := by
  match n with
  | ω =>
    intro m
    obtain ⟨u, hu, p, H, H'⟩ := h m
    exact ⟨{x ∈ u | f₁ x = f x}, Filter.inter_mem hu (mem_nhdsWithin_insert.2 ⟨hx, h₁⟩), p,
      (H.mono (sep_subset _ _)).congr fun _ ↦ And.right,
      fun i hi ↦ (H' i hi).mono (sep_subset _ _)⟩
  | (n : ℕ∞) =>
    intro m hm
    let ⟨u, hu, p, H⟩ := h m hm
    exact ⟨{ x ∈ u | f₁ x = f x }, Filter.inter_mem hu (mem_nhdsWithin_insert.2 ⟨hx, h₁⟩), p,
      (H.mono (sep_subset _ _)).congr fun _ ↦ And.right⟩

theorem ContDiffWithinAt.congr_of_eventuallyEq_insert (h : ContDiffWithinAt 𝕜 n f s x)
    (h₁ : f₁ =ᶠ[𝓝[insert x s] x] f) : ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr_of_eventuallyEq (nhdsWithin_mono x (subset_insert x s) h₁)
    (mem_of_mem_nhdsWithin (mem_insert x s) h₁ : _)

theorem ContDiffWithinAt.congr_of_eventually_eq' (h : ContDiffWithinAt 𝕜 n f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr_of_eventuallyEq h₁ <| h₁.self_of_nhdsWithin hx

theorem Filter.EventuallyEq.contDiffWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  ⟨fun H => ContDiffWithinAt.congr_of_eventuallyEq H h₁.symm hx.symm, fun H =>
    H.congr_of_eventuallyEq h₁ hx⟩

theorem ContDiffWithinAt.congr (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : ∀ y ∈ s, f₁ y = f y)
    (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem self_mem_nhdsWithin h₁) hx

theorem ContDiffWithinAt.congr' (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : ∀ y ∈ s, f₁ y = f y)
    (hx : x ∈ s) : ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr h₁ (h₁ _ hx)

theorem ContDiffWithinAt.mono_of_mem (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E}
    (hst : s ∈ 𝓝[t] x) : ContDiffWithinAt 𝕜 n f t x := by
  match n with
  | ω =>
    intro m
    obtain ⟨u, hu, p, H, H'⟩ := h m
    exact ⟨u, nhdsWithin_le_of_mem (insert_mem_nhdsWithin_insert hst) hu, p, H, H'⟩
  | (n : ℕ∞) =>
    intro m hm
    rcases h m hm with ⟨u, hu, p, H⟩
    exact ⟨u, nhdsWithin_le_of_mem (insert_mem_nhdsWithin_insert hst) hu, p, H⟩

theorem ContDiffWithinAt.mono (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : t ⊆ s) :
    ContDiffWithinAt 𝕜 n f t x :=
  h.mono_of_mem <| Filter.mem_of_superset self_mem_nhdsWithin hst

theorem ContDiffWithinAt.congr_nhds (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E}
    (hst : 𝓝[s] x = 𝓝[t] x) : ContDiffWithinAt 𝕜 n f t x :=
  h.mono_of_mem <| hst ▸ self_mem_nhdsWithin

theorem contDiffWithinAt_congr_nhds {t : Set E} (hst : 𝓝[s] x = 𝓝[t] x) :
    ContDiffWithinAt 𝕜 n f s x ↔ ContDiffWithinAt 𝕜 n f t x :=
  ⟨fun h => h.congr_nhds hst, fun h => h.congr_nhds hst.symm⟩

theorem contDiffWithinAt_inter' (h : t ∈ 𝓝[s] x) :
    ContDiffWithinAt 𝕜 n f (s ∩ t) x ↔ ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAt_congr_nhds <| Eq.symm <| nhdsWithin_restrict'' _ h

theorem contDiffWithinAt_inter (h : t ∈ 𝓝 x) :
    ContDiffWithinAt 𝕜 n f (s ∩ t) x ↔ ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAt_inter' (mem_nhdsWithin_of_mem_nhds h)

theorem contDiffWithinAt_insert_self :
    ContDiffWithinAt 𝕜 n f (insert x s) x ↔ ContDiffWithinAt 𝕜 n f s x := by
  match n with
  | ω => simp [ContDiffWithinAt]
  | (n : ℕ∞) => simp_rw [ContDiffWithinAt, insert_idem]

theorem contDiffWithinAt_insert {y : E} :
    ContDiffWithinAt 𝕜 n f (insert y s) x ↔ ContDiffWithinAt 𝕜 n f s x := by
  rcases eq_or_ne x y with (rfl | hx)
  · exact contDiffWithinAt_insert_self
  refine ⟨fun h ↦ h.mono (subset_insert _ _), fun h ↦ ?_⟩
  apply h.mono_of_mem
  simp [nhdsWithin_insert_of_ne hx, self_mem_nhdsWithin]

alias ⟨ContDiffWithinAt.of_insert, ContDiffWithinAt.insert'⟩ := contDiffWithinAt_insert

protected theorem ContDiffWithinAt.insert (h : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n f (insert x s) x :=
  h.insert'

/-- If a function is `C^n` within a set at a point, with `n ≥ 1`, then it is differentiable
within this set at this point. -/
theorem ContDiffWithinAt.differentiable_within_at' (h : ContDiffWithinAt 𝕜 n f s x) (hn : 1 ≤ n) :
    DifferentiableWithinAt 𝕜 f (insert x s) x := by
  rcases contDiffWithinAt_nat.1 (h.of_le hn) with ⟨u, hu, p, H⟩
  rcases mem_nhdsWithin.1 hu with ⟨t, t_open, xt, tu⟩
  rw [inter_comm] at tu
  have := ((H.mono tu).differentiableOn le_rfl) x ⟨mem_insert x s, xt⟩
  exact (differentiableWithinAt_inter (IsOpen.mem_nhds t_open xt)).1 this

theorem ContDiffWithinAt.differentiableWithinAt (h : ContDiffWithinAt 𝕜 n f s x) (hn : 1 ≤ n) :
    DifferentiableWithinAt 𝕜 f s x :=
  (h.differentiable_within_at' hn).mono (subset_insert x s)

/-- A function is `C^(n + 1)` on a domain iff locally, it has a derivative which is `C^n`. -/
theorem contDiffWithinAt_succ_iff_hasFDerivWithinAt {n : ℕ} :
    ContDiffWithinAt 𝕜 (n + 1 : ℕ) f s x ↔ ∃ u ∈ 𝓝[insert x s] x, ∃ f' : E → E →L[𝕜] F,
      (∀ x ∈ u, HasFDerivWithinAt f (f' x) u x) ∧ ContDiffWithinAt 𝕜 n f' u x := by
  constructor
  · intro h
    rcases h n.succ le_rfl with ⟨u, hu, p, Hp⟩
    refine
      ⟨u, hu, fun y => (continuousMultilinearCurryFin1 𝕜 E F) (p y 1), fun y hy =>
        Hp.hasFDerivWithinAt (WithTop.coe_le_coe.2 (Nat.le_add_left 1 n)) hy, ?_⟩
    intro m hm
    refine ⟨u, ?_, fun y : E => (p y).shift, ?_⟩
    · -- Porting note: without the explicit argument Lean is not sure of the type.
      convert @self_mem_nhdsWithin _ _ x u
      have : x ∈ insert x s := by simp
      exact insert_eq_of_mem (mem_of_mem_nhdsWithin this hu)
    · rw [hasFTaylorSeriesUpToOn_succ_nat_iff_right] at Hp
      exact Hp.2.2.of_le hm
  · rintro ⟨u, hu, f', f'_eq_deriv, Hf'⟩
    rw [contDiffWithinAt_nat]
    rcases Hf' n le_rfl with ⟨v, hv, p', Hp'⟩
    refine ⟨v ∩ u, ?_, fun x => (p' x).unshift (f x), ?_⟩
    · apply Filter.inter_mem _ hu
      apply nhdsWithin_le_of_mem hu
      exact nhdsWithin_mono _ (subset_insert x u) hv
    · rw [hasFTaylorSeriesUpToOn_succ_nat_iff_right]
      refine ⟨fun y _ => rfl, fun y hy => ?_, ?_⟩
      · change
          HasFDerivWithinAt (fun z => (continuousMultilinearCurryFin0 𝕜 E F).symm (f z))
            (FormalMultilinearSeries.unshift (p' y) (f y) 1).curryLeft (v ∩ u) y
        -- Porting note: needed `erw` here.
        -- https://github.com/leanprover-community/mathlib4/issues/5164
        erw [LinearIsometryEquiv.comp_hasFDerivWithinAt_iff']
        convert (f'_eq_deriv y hy.2).mono inter_subset_right
        rw [← Hp'.zero_eq y hy.1]
        ext z
        change ((p' y 0) (init (@cons 0 (fun _ => E) z 0))) (@cons 0 (fun _ => E) z 0 (last 0)) =
          ((p' y 0) 0) z
        congr
        norm_num [eq_iff_true_of_subsingleton]
      · convert (Hp'.mono inter_subset_left).congr fun x hx => Hp'.zero_eq x hx.1 using 1
        · ext x y
          change p' x 0 (init (@snoc 0 (fun _ : Fin 1 => E) 0 y)) y = p' x 0 0 y
          rw [init_snoc]
        · ext x k v y
          change p' x k (init (@snoc k (fun _ : Fin k.succ => E) v y))
            (@snoc k (fun _ : Fin k.succ => E) v y (last k)) = p' x k v y
          rw [snoc_last, init_snoc]

/-- A version of `contDiffWithinAt_succ_iff_hasFDerivWithinAt` where all derivatives
  are taken within the same set. -/
theorem contDiffWithinAt_succ_iff_hasFDerivWithinAt' {n : ℕ} :
    ContDiffWithinAt 𝕜 (n + 1 : ℕ) f s x ↔
      ∃ u ∈ 𝓝[insert x s] x, u ⊆ insert x s ∧ ∃ f' : E → E →L[𝕜] F,
        (∀ x ∈ u, HasFDerivWithinAt f (f' x) s x) ∧ ContDiffWithinAt 𝕜 n f' s x := by
  refine ⟨fun hf => ?_, ?_⟩
  · obtain ⟨u, hu, f', huf', hf'⟩ := contDiffWithinAt_succ_iff_hasFDerivWithinAt.mp hf
    obtain ⟨w, hw, hxw, hwu⟩ := mem_nhdsWithin.mp hu
    rw [inter_comm] at hwu
    refine ⟨insert x s ∩ w, inter_mem_nhdsWithin _ (hw.mem_nhds hxw), inter_subset_left, f',
      fun y hy => ?_, ?_⟩
    · refine ((huf' y <| hwu hy).mono hwu).mono_of_mem ?_
      refine mem_of_superset ?_ (inter_subset_inter_left _ (subset_insert _ _))
      exact inter_mem_nhdsWithin _ (hw.mem_nhds hy.2)
    · exact hf'.mono_of_mem (nhdsWithin_mono _ (subset_insert _ _) hu)
  · rw [← contDiffWithinAt_insert, contDiffWithinAt_succ_iff_hasFDerivWithinAt,
      insert_eq_of_mem (mem_insert _ _)]
    rintro ⟨u, hu, hus, f', huf', hf'⟩
    exact ⟨u, hu, f', fun y hy => (huf' y hy).insert'.mono hus, hf'.insert.mono hus⟩

/- A function is `C^ω` on a domain iff locally, it is analytic with a derivative which is `C^ω`. -/
/-theorem contDiffWithinAt_omega_iff_hasFDerivWithinAt :
    ContDiffWithinAt 𝕜 ω f s x ↔
      ∀ (m : ℕ), ∃ u ∈ 𝓝[insert x s] x, AnalyticWithinOn 𝕜 f u ∧ ∃ f' : E → E →L[𝕜] F,
        ∃ (p : E → FormalMultilinearSeries 𝕜 E (E →L[𝕜] F)),
        (∀ x ∈ u, HasFDerivWithinAt f (f' x) u x) ∧ (HasFTaylorSeriesUpToOn m f' p u)
        ∧ (∀ i ≤ m, AnalyticWithinOn 𝕜 (fun x ↦ p x i) u) := by
  constructor
  · intro h m
    obtain ⟨v, v_mem, hv⟩ := h.analyticWithinOn
    obtain ⟨u, hu, p, Hp, hp⟩ := h (m + 1)
    have hm : (1 : ℕ∞) ≤ (m + 1 : ℕ) := by norm_cast; linarith
    refine
      ⟨u ∩ v, inter_mem hu v_mem, hv.mono inter_subset_right,
        fun y => (continuousMultilinearCurryFin1 𝕜 E F) (p y 1), fun y : E => (p y).shift,
        fun y hy ↦ (Hp.mono inter_subset_left).hasFDerivWithinAt hm hy, ?_, ?_⟩
    · rw [hasFTaylorSeriesUpToOn_succ_nat_iff_right] at Hp
      exact Hp.2.2.mono inter_subset_left
    · intro i hi
      change AnalyticWithinOn 𝕜
        (fun x ↦ (continuousMultilinearCurryRightEquiv' 𝕜 i E F).symm (p x (i + 1))) (u ∩ v)
      exact (LinearIsometryEquiv.analyticOn _ _).comp_analyticWithinOn
        ((hp (i + 1) (by linarith)).mono inter_subset_left) (Set.mapsTo_univ _ _)
  · intro h m
    obtain ⟨u, hu, hf, f', p', f'_eq_deriv, hp, Hf'⟩ := h m
    refine ⟨u, hu, fun x => (p' x).unshift (f x), ?_, ?_⟩
    · cases m with
      | zero =>
          simp only [CharP.cast_eq_zero, hasFTaylorSeriesUpToOn_zero_iff]
          exact ⟨hf.continuousOn, fun x _ ↦ rfl⟩
      | succ m =>
        rw [hasFTaylorSeriesUpToOn_succ_nat_iff_right]
        refine ⟨fun y _ => rfl, fun y hy ↦ ?_, ?_⟩
        · change
            HasFDerivWithinAt (fun z => (continuousMultilinearCurryFin0 𝕜 E F).symm (f z))
              (FormalMultilinearSeries.unshift (p' y) (f y) 1).curryLeft u y
          -- Porting note: needed `erw` here.
          -- https://github.com/leanprover-community/mathlib4/issues/5164
          erw [LinearIsometryEquiv.comp_hasFDerivWithinAt_iff']
          convert f'_eq_deriv y hy
          rw [← hp.zero_eq y hy]
          ext z
          change ((p' y 0) (init (@cons 0 (fun _ => E) z 0))) (@cons 0 (fun _ => E) z 0 (last 0)) =
            ((p' y 0) 0) z
          congr
          norm_num [eq_iff_true_of_subsingleton]
        · have h'm : (m : ℕ∞) ≤ (m + 1 : ℕ) := by norm_cast; linarith
          convert (hp.of_le h'm).congr fun x hx => hp.zero_eq x hx using 1
          · ext x y
            change p' x 0 (init (@snoc 0 (fun _ : Fin 1 => E) 0 y)) y = p' x 0 0 y
            rw [init_snoc]
          · ext x k v y
            change p' x k (init (@snoc k (fun _ : Fin k.succ => E) v y))
              (@snoc k (fun _ : Fin k.succ => E) v y (last k)) = p' x k v y
            rw [snoc_last, init_snoc]
    · intro i hi
      match i with
      | 0 =>
        simp only [FormalMultilinearSeries.unshift]
        apply AnalyticOn.comp_analyticWithinOn ?_ hf (Set.mapsTo_univ _ _)
        exact LinearIsometryEquiv.analyticOn _ _
      | (i + 1) =>
        simp only [FormalMultilinearSeries.unshift, Nat.succ_eq_add_one]
        apply AnalyticOn.comp_analyticWithinOn ?_ (Hf' i (by linarith)) (Set.mapsTo_univ _ _)
        exact LinearIsometryEquiv.analyticOn _ _
-/

/-! ### Smooth functions within a set -/

variable (𝕜)

/-- A function is continuously differentiable up to `n` on `s` if, for any point `x` in `s`, it
admits continuous derivatives up to order `n` on a neighborhood of `x` in `s`.

For `n = ∞`, we only require that this holds up to any finite order (where the neighborhood may
depend on the finite order we consider).
-/
def ContDiffOn (n : WithTop (ℕ∞)) (f : E → F) (s : Set E) : Prop :=
  ∀ x ∈ s, ContDiffWithinAt 𝕜 n f s x

/-- Splitting out a part of the definition of `C^ω` functions of a domain. Implementation detail,
only to be used for API development of `C^ω` functions. -/
def ContDiffOnOmegaAux (n : ℕ) (f : E → F) (s : Set E) : Prop :=
  ∀ x ∈ s, ContDiffWithinAtOmegaAux 𝕜 n f s x

variable {𝕜}

lemma ContDiffOnOmegaAux.of_le {m n : ℕ} (h : ContDiffOnOmegaAux 𝕜 n f s) (h' : m ≤ n) :
    ContDiffOnOmegaAux 𝕜 m f s := by
  intro x hx
  rcases h x hx with ⟨u, hu, p, hp, h'p⟩
  exact ⟨u, hu, p, hp.of_le (by simp [h']), fun i hi ↦ h'p i (hi.trans h')⟩

lemma contDiffOnOmegaAux_zero :
    ContDiffOnOmegaAux 𝕜 0 f s ↔ AnalyticWithinOn 𝕜 f s := by
  refine ⟨fun h x hx ↦ (h x hx).analyticWithinAt , fun h x hx ↦ ?_⟩
  refine ⟨s, ?_, ftaylorSeriesWithin 𝕜 f s, ?_, ?_⟩
  · rw [insert_eq_of_mem hx]
    exact self_mem_nhdsWithin
  · simp only [CharP.cast_eq_zero, hasFTaylorSeriesUpToOn_zero_iff]
    refine ⟨h.continuousOn, fun x _ ↦ rfl⟩
  · simp only [nonpos_iff_eq_zero, forall_eq, ftaylorSeriesWithin,
      iteratedFDerivWithin_zero_eq_comp]
    exact AnalyticOn.comp_analyticWithinOn (LinearIsometryEquiv.analyticOn _ _) h
      (Set.mapsTo_univ _ _)

theorem HasFTaylorSeriesUpToOn.contDiffOn {n : ℕ∞} {f' : E → FormalMultilinearSeries 𝕜 E F}
    (hf : HasFTaylorSeriesUpToOn n f f' s) : ContDiffOn 𝕜 n f s := by
  intro x hx m hm
  use s
  simp only [Set.insert_eq_of_mem hx, self_mem_nhdsWithin, true_and_iff]
  exact ⟨f', hf.of_le hm⟩

theorem ContDiffOn.contDiffWithinAt (h : ContDiffOn 𝕜 n f s) (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 n f s x :=
  h x hx

theorem ContDiffWithinAt.contDiffOn' {m : ℕ} (hm : (m : ℕ∞) ≤ n)
    (h : ContDiffWithinAt 𝕜 n f s x) :
    ∃ u, IsOpen u ∧ x ∈ u ∧ ContDiffOn 𝕜 m f (insert x s ∩ u) := by
  rcases contDiffWithinAt_nat.1 (h.of_le hm) with ⟨t, ht, p, hp⟩
  rcases mem_nhdsWithin.1 ht with ⟨u, huo, hxu, hut⟩
  rw [inter_comm] at hut
  exact ⟨u, huo, hxu, (hp.mono hut).contDiffOn⟩

theorem ContDiffWithinAt.contDiffOn {m : ℕ} (hm : (m : ℕ∞) ≤ n) (h : ContDiffWithinAt 𝕜 n f s x) :
    ∃ u ∈ 𝓝[insert x s] x, u ⊆ insert x s ∧ ContDiffOn 𝕜 m f u :=
  let ⟨_u, uo, xu, h⟩ := h.contDiffOn' hm
  ⟨_, inter_mem_nhdsWithin _ (uo.mem_nhds xu), inter_subset_left, h⟩

theorem ContDiffOn.analyticWithinOn (h : ContDiffOn 𝕜 ω f s) : AnalyticWithinOn 𝕜 f s :=
  fun x hx ↦ (h x hx).analyticWithinAt

protected theorem ContDiffWithinAt.eventually {n : ℕ} (h : ContDiffWithinAt 𝕜 n f s x) :
    ∀ᶠ y in 𝓝[insert x s] x, ContDiffWithinAt 𝕜 n f s y := by
  rcases h.contDiffOn le_rfl with ⟨u, hu, _, hd⟩
  have : ∀ᶠ y : E in 𝓝[insert x s] x, u ∈ 𝓝[insert x s] y ∧ y ∈ u :=
    (eventually_nhdsWithin_nhdsWithin.2 hu).and hu
  refine this.mono fun y hy => (hd y hy.2).mono_of_mem ?_
  exact nhdsWithin_mono y (subset_insert _ _) hy.1

theorem ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m ≤ n) : ContDiffOn 𝕜 m f s := fun x hx =>
  (h x hx).of_le hmn

theorem ContDiffOn.of_succ {n : ℕ} (h : ContDiffOn 𝕜 (n + 1) f s) : ContDiffOn 𝕜 n f s :=
  h.of_le <| WithTop.coe_le_coe.mpr le_self_add

theorem ContDiffOn.one_of_succ {n : ℕ} (h : ContDiffOn 𝕜 (n + 1) f s) : ContDiffOn 𝕜 1 f s :=
  h.of_le <| WithTop.coe_le_coe.mpr le_add_self

theorem contDiffOn_iff_forall_nat_le {n : ℕ∞} :
    ContDiffOn 𝕜 n f s ↔ ∀ m : ℕ, ↑m ≤ n → ContDiffOn 𝕜 m f s :=
  ⟨fun H _ hm => H.of_le (by exact_mod_cast hm), fun H x hx m hm => H m hm x hx m le_rfl⟩

theorem contDiffOn_top : ContDiffOn 𝕜 ∞ f s ↔ ∀ n : ℕ, ContDiffOn 𝕜 n f s :=
  contDiffOn_iff_forall_nat_le.trans <| by simp only [le_top, forall_prop_of_true]

theorem contDiffOn_all_iff_nat :
    (∀ (n : ℕ∞), ContDiffOn 𝕜 n f s) ↔ ∀ n : ℕ, ContDiffOn 𝕜 n f s := by
  refine ⟨fun H n => H n, ?_⟩
  rintro H (_ | n)
  exacts [contDiffOn_top.2 H, H n]

theorem ContDiffOn.continuousOn (h : ContDiffOn 𝕜 n f s) : ContinuousOn f s := fun x hx =>
  (h x hx).continuousWithinAt

theorem ContDiffOn.congr (h : ContDiffOn 𝕜 n f s) (h₁ : ∀ x ∈ s, f₁ x = f x) :
    ContDiffOn 𝕜 n f₁ s := fun x hx => (h x hx).congr h₁ (h₁ x hx)

theorem contDiffOn_congr (h₁ : ∀ x ∈ s, f₁ x = f x) : ContDiffOn 𝕜 n f₁ s ↔ ContDiffOn 𝕜 n f s :=
  ⟨fun H => H.congr fun x hx => (h₁ x hx).symm, fun H => H.congr h₁⟩

theorem ContDiffOn.mono (h : ContDiffOn 𝕜 n f s) {t : Set E} (hst : t ⊆ s) : ContDiffOn 𝕜 n f t :=
  fun x hx => (h x (hst hx)).mono hst

theorem ContDiffOn.congr_mono (hf : ContDiffOn 𝕜 n f s) (h₁ : ∀ x ∈ s₁, f₁ x = f x) (hs : s₁ ⊆ s) :
    ContDiffOn 𝕜 n f₁ s₁ :=
  (hf.mono hs).congr h₁

/-- If a function is `C^n` on a set with `n ≥ 1`, then it is differentiable there. -/
theorem ContDiffOn.differentiableOn (h : ContDiffOn 𝕜 n f s) (hn : 1 ≤ n) :
    DifferentiableOn 𝕜 f s := fun x hx => (h x hx).differentiableWithinAt hn

/-- If a function is `C^n` around each point in a set, then it is `C^n` on the set. -/
theorem contDiffOn_of_locally_contDiffOn
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ ContDiffOn 𝕜 n f (s ∩ u)) : ContDiffOn 𝕜 n f s := by
  intro x xs
  rcases h x xs with ⟨u, u_open, xu, hu⟩
  apply (contDiffWithinAt_inter _).1 (hu x ⟨xs, xu⟩)
  exact IsOpen.mem_nhds u_open xu

/-- A function is `C^(n + 1)` on a domain iff locally, it has a derivative which is `C^n`. -/
theorem contDiffOn_succ_iff_hasFDerivWithinAt {n : ℕ} :
    ContDiffOn 𝕜 (n + 1 : ℕ) f s ↔
      ∀ x ∈ s, ∃ u ∈ 𝓝[insert x s] x, ∃ f' : E → E →L[𝕜] F,
        (∀ x ∈ u, HasFDerivWithinAt f (f' x) u x) ∧ ContDiffOn 𝕜 n f' u := by
  constructor
  · intro h x hx
    rcases (h x hx) n.succ le_rfl with ⟨u, hu, p, Hp⟩
    refine
      ⟨u, hu, fun y => (continuousMultilinearCurryFin1 𝕜 E F) (p y 1), fun y hy =>
        Hp.hasFDerivWithinAt (WithTop.coe_le_coe.2 (Nat.le_add_left 1 n)) hy, ?_⟩
    rw [hasFTaylorSeriesUpToOn_succ_nat_iff_right] at Hp
    intro z hz m hm
    refine ⟨u, ?_, fun x : E => (p x).shift, Hp.2.2.of_le hm⟩
    -- Porting note: without the explicit arguments `convert` can not determine the type.
    convert @self_mem_nhdsWithin _ _ z u
    exact insert_eq_of_mem hz
  · intro h x hx
    rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt]
    rcases h x hx with ⟨u, u_nhbd, f', hu, hf'⟩
    have : x ∈ u := mem_of_mem_nhdsWithin (mem_insert _ _) u_nhbd
    exact ⟨u, u_nhbd, f', hu, hf' x this⟩

lemma foo {s t u : Set E} (hs : t ∈ 𝓝[u] x) (h' : s ∈ 𝓝[t] x) : s ∈ 𝓝[u] x := by
  apply nhdsWithin_le_of_mem hs h'

/-- A function is `C^(n + 1)` on a domain iff locally, it has a derivative which is `C^n`. -/
theorem contDiffOnOmegaAux_succ_iff_hasFDerivWithinAt {n : ℕ} :
    ContDiffOnOmegaAux 𝕜 (n + 1 : ℕ) f s ↔
      ∀ x ∈ s, ∃ u ∈ 𝓝[insert x s] x, AnalyticWithinOn 𝕜 f u ∧ ∃ f' : E → E →L[𝕜] F,
        (∀ x ∈ u, HasFDerivWithinAt f (f' x) u x) ∧ ContDiffOnOmegaAux 𝕜 n f' u := by
  constructor
  · intro h x hx
    rcases (h x hx) with ⟨u, hu, p, Hp, hp⟩
    rw [insert_eq_of_mem hx] at hu ⊢
    refine ⟨s ∩ u, inter_mem self_mem_nhdsWithin hu,
      (contDiffOnOmegaAux_zero.1 (h.of_le (zero_le _))).mono inter_subset_left,
      fun y => (continuousMultilinearCurryFin1 𝕜 E F) (p y 1),
      fun y hy ↦ (Hp.hasFDerivWithinAt (by simp) hy.2).mono inter_subset_right, ?_⟩
    rw [hasFTaylorSeriesUpToOn_succ_nat_iff_right] at Hp
    intro z hz
    refine ⟨s ∩ u, ?_, fun z : E => (p z).shift, Hp.2.2.mono inter_subset_right, ?_⟩
    · rw [insert_eq_of_mem hz]
      exact self_mem_nhdsWithin
    · intro i hi
      change AnalyticWithinOn 𝕜
        (fun x ↦ (continuousMultilinearCurryRightEquiv' 𝕜 i E F).symm (p x (i + 1))) (s ∩ u)
      exact (LinearIsometryEquiv.analyticOn _ _).comp_analyticWithinOn
        ((hp (i + 1) (by linarith)).mono inter_subset_right) (Set.mapsTo_univ _ _)
  · intro h x hx
    rcases h x hx with ⟨u, hu, hf, f', f'_eq_deriv, Hf'⟩
    have xu : x ∈ u := mem_of_mem_nhdsWithin (by simp) hu
    rcases Hf' x xu with ⟨v, hv, p', hp, h'p⟩
    refine ⟨u ∩ v, ?_, fun y => (p' y).unshift (f y), ?_, ?_⟩
    · simp only [insert_eq_of_mem, hx, xu] at hu hv ⊢
      exact inter_mem hu (nhdsWithin_le_of_mem hu hv)
    · rw [hasFTaylorSeriesUpToOn_succ_nat_iff_right]
      refine ⟨fun y _ => rfl, fun y hy ↦ ?_, ?_⟩
      · erw [LinearIsometryEquiv.comp_hasFDerivWithinAt_iff']
        convert (f'_eq_deriv y hy.1).mono inter_subset_left
        rw [← hp.zero_eq y hy.2]
        ext z
        change ((p' y 0) (init (@cons 0 (fun _ => E) z 0))) (@cons 0 (fun _ => E) z 0 (last 0)) =
          ((p' y 0) 0) z
        congr
        norm_num [eq_iff_true_of_subsingleton]
      · convert (hp.mono inter_subset_right).congr fun x hx => hp.zero_eq x hx.2 using 1
        · ext x y
          change p' x 0 (init (@snoc 0 (fun _ : Fin 1 => E) 0 y)) y = p' x 0 0 y
          rw [init_snoc]
        · ext x k v y
          change p' x k (init (@snoc k (fun _ : Fin k.succ => E) v y))
            (@snoc k (fun _ : Fin k.succ => E) v y (last k)) = p' x k v y
          rw [snoc_last, init_snoc]
    · intro i hi
      match i with
      | 0 =>
        simp only [FormalMultilinearSeries.unshift]
        apply AnalyticOn.comp_analyticWithinOn ?_ (hf.mono inter_subset_left) (Set.mapsTo_univ _ _)
        exact LinearIsometryEquiv.analyticOn _ _
      | (i + 1) =>
        simp only [FormalMultilinearSeries.unshift, Nat.succ_eq_add_one]
        apply AnalyticOn.comp_analyticWithinOn ?_ ((h'p i (by linarith)).mono inter_subset_right)
          (Set.mapsTo_univ _ _)
        exact LinearIsometryEquiv.analyticOn _ _




/- A function is `C^ω` on a domain iff locally, it is analytic with a derivative which is `C^ω`. -/
/-theorem contDiffOn_omega_iff_hasFDerivWithinAt :
    ContDiffOn 𝕜 ω f s ↔
      ∀ x ∈ s, ∃ u ∈ 𝓝[insert x s] x, AnalyticWithinOn 𝕜 f u ∧ ∃ f' : E → E →L[𝕜] F,
        (∀ x ∈ u, HasFDerivWithinAt f (f' x) u x) ∧ ContDiffWithinAt 𝕜 ⊤ f' u x := by
  constructor
  · intro h x hx
    exact contDiffWithinAt_omega_iff_hasFDerivWithinAt.1 (h x hx)
  · intro h x hx
    exact contDiffWithinAt_omega_iff_hasFDerivWithinAt.2 (h x hx)
-/

/-! ### Iterated derivative within a set -/

@[simp]
theorem contDiffOn_zero : ContDiffOn 𝕜 0 f s ↔ ContinuousOn f s := by
  refine ⟨fun H => H.continuousOn, fun H => fun x hx m hm ↦ ?_⟩
  have : (m : ℕ∞) = 0 := le_antisymm hm bot_le
  rw [this]
  refine ⟨insert x s, self_mem_nhdsWithin, ftaylorSeriesWithin 𝕜 f s, ?_⟩
  rw [hasFTaylorSeriesUpToOn_zero_iff]
  exact ⟨by rwa [insert_eq_of_mem hx], fun x _ => by simp [ftaylorSeriesWithin]⟩

theorem contDiffWithinAt_zero (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 0 f s x ↔ ∃ u ∈ 𝓝[s] x, ContinuousOn f (s ∩ u) := by
  constructor
  · intro h
    obtain ⟨u, H, p, hp⟩ := h 0 le_rfl
    refine ⟨u, ?_, ?_⟩
    · simpa [hx] using H
    · simp only [Nat.cast_zero, hasFTaylorSeriesUpToOn_zero_iff] at hp
      exact hp.1.mono inter_subset_right
  · rintro ⟨u, H, hu⟩
    rw [← contDiffWithinAt_inter' H]
    have h' : x ∈ s ∩ u := ⟨hx, mem_of_mem_nhdsWithin hx H⟩
    exact (contDiffOn_zero.mpr hu).contDiffWithinAt h'

/-- When a function is `C^n` in a set `s` of unique differentiability, it admits
`ftaylorSeriesWithin 𝕜 f s` as a Taylor series up to order `n` in `s`. -/
protected theorem ContDiffOn.ftaylorSeriesWithin {n : ℕ∞}
    (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) :
    HasFTaylorSeriesUpToOn n f (ftaylorSeriesWithin 𝕜 f s) s := by
  constructor
  · intro x _
    simp only [ftaylorSeriesWithin, ContinuousMultilinearMap.uncurry0_apply,
      iteratedFDerivWithin_zero_apply]
  · intro m hm x hx
    rcases (h x hx) m.succ (Order.add_one_le_of_lt hm) with ⟨u, hu, p, Hp⟩
    rw [insert_eq_of_mem hx] at hu
    rcases mem_nhdsWithin.1 hu with ⟨o, o_open, xo, ho⟩
    rw [inter_comm] at ho
    have : p x m.succ = ftaylorSeriesWithin 𝕜 f s x m.succ := by
      change p x m.succ = iteratedFDerivWithin 𝕜 m.succ f s x
      rw [← iteratedFDerivWithin_inter_open o_open xo]
      exact (Hp.mono ho).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (hs.inter o_open) ⟨hx, xo⟩
    rw [← this, ← hasFDerivWithinAt_inter (IsOpen.mem_nhds o_open xo)]
    have A : ∀ y ∈ s ∩ o, p y m = ftaylorSeriesWithin 𝕜 f s y m := by
      rintro y ⟨hy, yo⟩
      change p y m = iteratedFDerivWithin 𝕜 m f s y
      rw [← iteratedFDerivWithin_inter_open o_open yo]
      exact
        (Hp.mono ho).eq_iteratedFDerivWithin_of_uniqueDiffOn (WithTop.coe_le_coe.2 (Nat.le_succ m))
          (hs.inter o_open) ⟨hy, yo⟩
    exact
      ((Hp.mono ho).fderivWithin m (WithTop.coe_lt_coe.2 (lt_add_one m)) x ⟨hx, xo⟩).congr
        (fun y hy => (A y hy).symm) (A x ⟨hx, xo⟩).symm
  · intro m hm
    apply continuousOn_of_locally_continuousOn
    intro x hx
    rcases h x hx m hm with ⟨u, hu, p, Hp⟩
    rcases mem_nhdsWithin.1 hu with ⟨o, o_open, xo, ho⟩
    rw [insert_eq_of_mem hx] at ho
    rw [inter_comm] at ho
    refine ⟨o, o_open, xo, ?_⟩
    have A : ∀ y ∈ s ∩ o, p y m = ftaylorSeriesWithin 𝕜 f s y m := by
      rintro y ⟨hy, yo⟩
      change p y m = iteratedFDerivWithin 𝕜 m f s y
      rw [← iteratedFDerivWithin_inter_open o_open yo]
      exact (Hp.mono ho).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (hs.inter o_open) ⟨hy, yo⟩
    exact ((Hp.mono ho).cont m le_rfl).congr fun y hy => (A y hy).symm

/-- When a function is `C^ω` in a set `s` of unique differentiability, then its iterated derivatives
within `s` are analytic. -/
protected theorem ContDiffOn.analyticWithinOn_iteratedFDerivWithin
    (h : ContDiffOn 𝕜 ω f s) (hs : UniqueDiffOn 𝕜 s) (n : ℕ) :
    AnalyticWithinOn 𝕜 (iteratedFDerivWithin 𝕜 n f s) s := by
  intro x hx
  rcases h x hx n with ⟨u, hu, p, Hp, h'p⟩
  rcases mem_nhdsWithin.1 hu with ⟨o, o_open, xo, ho⟩
  rw [inter_comm] at ho
  suffices AnalyticWithinAt 𝕜 (iteratedFDerivWithin 𝕜 n f s) (s ∩ o) x from
    this.mono_of_mem (inter_mem_nhdsWithin _ (o_open.mem_nhds xo))
  suffices EqOn (iteratedFDerivWithin 𝕜 n f s) (fun x ↦ p x n) (s ∩ o) by
    have A : AnalyticWithinOn 𝕜 (fun x ↦ p x n) (s ∩ o) :=
      (h'p n le_rfl).mono <| Subset.trans (inter_subset_inter_left _ (subset_insert _ _)) ho
    exact A.congr this x ⟨hx, xo⟩
  rintro y ⟨hy, yo⟩
  rw [← iteratedFDerivWithin_inter_open o_open yo]
  symm
  simpa [hx, hy, yo, hs.inter o_open]
    using (Hp.mono ho).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (x := y)

theorem contDiffOn_of_continuousOn_differentiableOn {n : ℕ∞}
    (Hcont : ∀ m : ℕ, (m : ℕ∞) ≤ n → ContinuousOn (fun x => iteratedFDerivWithin 𝕜 m f s x) s)
    (Hdiff : ∀ m : ℕ, (m : ℕ∞) < n →
      DifferentiableOn 𝕜 (fun x => iteratedFDerivWithin 𝕜 m f s x) s) :
    ContDiffOn 𝕜 n f s := by
  intro x hx m hm
  rw [insert_eq_of_mem hx]
  refine ⟨s, self_mem_nhdsWithin, ftaylorSeriesWithin 𝕜 f s, ?_⟩
  constructor
  · intro y _
    simp only [ftaylorSeriesWithin, ContinuousMultilinearMap.uncurry0_apply,
      iteratedFDerivWithin_zero_apply]
  · intro k hk y hy
    convert (Hdiff k (lt_of_lt_of_le hk hm) y hy).hasFDerivWithinAt
  · intro k hk
    exact Hcont k (le_trans hk hm)

theorem contDiffOn_of_differentiableOn {n : ℕ∞}
    (h : ∀ m : ℕ, (m : ℕ∞) ≤ n → DifferentiableOn 𝕜 (iteratedFDerivWithin 𝕜 m f s) s) :
    ContDiffOn 𝕜 n f s :=
  contDiffOn_of_continuousOn_differentiableOn (fun m hm => (h m hm).continuousOn) fun m hm =>
    h m (le_of_lt hm)

theorem contDiffOn_of_analyticWithinOn_iteratedFDerivWithin
    (h : ∀ m, AnalyticWithinOn 𝕜 (iteratedFDerivWithin 𝕜 m f s) s) :
    ContDiffOn 𝕜 n f s := by
  suffices ContDiffOn 𝕜 ω f s from this.of_le le_top
  intro x hx m
  refine ⟨insert x s, self_mem_nhdsWithin, ftaylorSeriesWithin 𝕜 f s, ?_, ?_⟩
  · rw [insert_eq_of_mem hx]
    constructor
    · intro y _
      simp only [ftaylorSeriesWithin, ContinuousMultilinearMap.uncurry0_apply,
        iteratedFDerivWithin_zero_apply]
    · intro k _ y hy
      exact ((h k).differentiableOn y hy).hasFDerivWithinAt
    · intro k _
      exact (h k).continuousOn
  · intro i _
    rw [insert_eq_of_mem hx]
    exact h i

theorem contDiffOn_omega_iff_analyticWithinOn_iteratedFDerivWithin (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 ω f s ↔ ∀ m, AnalyticWithinOn 𝕜 (iteratedFDerivWithin 𝕜 m f s) s :=
  ⟨fun h m ↦ h.analyticWithinOn_iteratedFDerivWithin hs m,
  fun h ↦ contDiffOn_of_analyticWithinOn_iteratedFDerivWithin h⟩

theorem ContDiffOn.continuousOn_iteratedFDerivWithin {m : ℕ} (h : ContDiffOn 𝕜 n f s)
    (hmn : (m : ℕ∞) ≤ n) (hs : UniqueDiffOn 𝕜 s) : ContinuousOn (iteratedFDerivWithin 𝕜 m f s) s :=
  ((h.of_le hmn).ftaylorSeriesWithin hs).cont m le_rfl

theorem ContDiffOn.differentiableOn_iteratedFDerivWithin {m : ℕ} (h : ContDiffOn 𝕜 n f s)
    (hmn : (m : ℕ∞) < n) (hs : UniqueDiffOn 𝕜 s) :
    DifferentiableOn 𝕜 (iteratedFDerivWithin 𝕜 m f s) s := by
  intro x hx
  have : (m + 1 : ℕ) ≤ n := ENat.add_one_nat_le_withTop_of_lt hmn
  apply (((h.of_le this).ftaylorSeriesWithin hs).fderivWithin m ?_ x hx).differentiableWithinAt
  simp only [Nat.cast_lt, lt_add_iff_pos_right, _root_.zero_lt_one]

theorem ContDiffWithinAt.differentiableWithinAt_iteratedFDerivWithin {m : ℕ}
    (h : ContDiffWithinAt 𝕜 n f s x) (hmn : (m : ℕ∞) < n) (hs : UniqueDiffOn 𝕜 (insert x s)) :
    DifferentiableWithinAt 𝕜 (iteratedFDerivWithin 𝕜 m f s) s x := by
  rcases h.contDiffOn' (ENat.add_one_nat_le_withTop_of_lt hmn) with ⟨u, uo, xu, hu⟩
  set t := insert x s ∩ u
  have A : t =ᶠ[𝓝[≠] x] s := by
    simp only [set_eventuallyEq_iff_inf_principal, ← nhdsWithin_inter']
    rw [← inter_assoc, nhdsWithin_inter_of_mem', ← diff_eq_compl_inter, insert_diff_of_mem,
      diff_eq_compl_inter]
    exacts [rfl, mem_nhdsWithin_of_mem_nhds (uo.mem_nhds xu)]
  have B : iteratedFDerivWithin 𝕜 m f s =ᶠ[𝓝 x] iteratedFDerivWithin 𝕜 m f t :=
    iteratedFDerivWithin_eventually_congr_set' _ A.symm _
  have C : DifferentiableWithinAt 𝕜 (iteratedFDerivWithin 𝕜 m f t) t x :=
    hu.differentiableOn_iteratedFDerivWithin (Nat.cast_lt.2 m.lt_succ_self) (hs.inter uo) x
      ⟨mem_insert _ _, xu⟩
  rw [differentiableWithinAt_congr_set' _ A] at C
  exact C.congr_of_eventuallyEq (B.filter_mono inf_le_left) B.self_of_nhds

theorem contDiffOn_iff_continuousOn_differentiableOn {n : ℕ∞} (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 n f s ↔
      (∀ m : ℕ, (m : ℕ∞) ≤ n → ContinuousOn (fun x => iteratedFDerivWithin 𝕜 m f s x) s) ∧
        ∀ m : ℕ, (m : ℕ∞) < n → DifferentiableOn 𝕜 (fun x => iteratedFDerivWithin 𝕜 m f s x) s :=
  ⟨fun h => ⟨fun _m hm => h.continuousOn_iteratedFDerivWithin (by exact_mod_cast hm) hs,
      fun _m hm => h.differentiableOn_iteratedFDerivWithin (by exact_mod_cast hm) hs⟩,
    fun h => contDiffOn_of_continuousOn_differentiableOn h.1 h.2⟩

theorem contDiffOn_succ_of_fderivWithin {n : ℕ} (hf : DifferentiableOn 𝕜 f s)
    (h : ContDiffOn 𝕜 n (fun y => fderivWithin 𝕜 f s y) s) : ContDiffOn 𝕜 (n + 1 : ℕ) f s := by
  intro x hx
  rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt, insert_eq_of_mem hx]
  exact
    ⟨s, self_mem_nhdsWithin, fderivWithin 𝕜 f s, fun y hy => (hf y hy).hasFDerivWithinAt, h x hx⟩

theorem contDiffOn_of_analyticWithinOn_of_fderivWithin (hf : AnalyticWithinOn 𝕜 f s)
    (h : ContDiffOn 𝕜 ω (fun y ↦ fderivWithin 𝕜 f s y) s) : ContDiffOn 𝕜 n f s := by
  suffices ContDiffOn 𝕜 ω f s from this.of_le le_top
  suffices ∀ m, ContDiffOnOmegaAux 𝕜 (m + 1) f s from
    fun x hx m ↦ (this m).of_le (Nat.le_add_right m 1) x hx
  intro m
  apply contDiffOnOmegaAux_succ_iff_hasFDerivWithinAt.2 (fun x hx ↦ ?_)
  obtain ⟨v, hv, p, hp, h'p⟩ := h x hx m
  rw [insert_eq_of_mem hx] at hv ⊢
  refine ⟨s ∩ v, inter_mem self_mem_nhdsWithin hv, hf.mono inter_subset_left, fderivWithin 𝕜 f s,
    fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · exact (hf.differentiableOn y hy.1).hasFDerivWithinAt.mono inter_subset_left
  · exact h.mono inter_subset_left y hy m

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is
differentiable there, and its derivative (expressed with `fderivWithin`) is `C^n`. -/
theorem contDiffOn_succ_iff_fderivWithin {n : ℕ} (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 (n + 1 : ℕ) f s ↔
      DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 n (fun y => fderivWithin 𝕜 f s y) s := by
  refine ⟨fun H => ?_, fun h => contDiffOn_succ_of_fderivWithin h.1 h.2⟩
  refine ⟨H.differentiableOn (WithTop.coe_le_coe.2 (by simp)), fun x hx => ?_⟩
  rcases contDiffWithinAt_succ_iff_hasFDerivWithinAt.1 (H x hx) with ⟨u, hu, f', hff', hf'⟩
  rcases mem_nhdsWithin.1 hu with ⟨o, o_open, xo, ho⟩
  rw [inter_comm, insert_eq_of_mem hx] at ho
  have := hf'.mono ho
  rw [contDiffWithinAt_inter' (mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds o_open xo))] at this
  apply this.congr_of_eventually_eq' _ hx
  have : o ∩ s ∈ 𝓝[s] x := mem_nhdsWithin.2 ⟨o, o_open, xo, Subset.refl _⟩
  rw [inter_comm] at this
  refine Filter.eventuallyEq_of_mem this fun y hy => ?_
  have A : fderivWithin 𝕜 f (s ∩ o) y = f' y :=
    ((hff' y (ho hy)).mono ho).fderivWithin (hs.inter o_open y hy)
  rwa [fderivWithin_inter (o_open.mem_nhds hy.2)] at A

/-- A function is `C^ω` on a domain with unique derivatives if and only if it is
analytic there, and its derivative (expressed with `fderivWithin`) is `C^ω`. Note that the second
condition is not needed when the space is complete, see `AnalyticWithinOn.contDiffOn`. -/
theorem contDiffOn_omega_iff_fderivWithin (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 ω f s ↔
      AnalyticWithinOn 𝕜 f s ∧ ContDiffOn 𝕜 ω (fun y => fderivWithin 𝕜 f s y) s := by
  refine ⟨fun H => ?_, fun h => contDiffOn_of_analyticWithinOn_of_fderivWithin h.1 h.2⟩
  refine ⟨H.analyticWithinOn, fun x hx m => ?_⟩
  rcases contDiffWithinAt_omega_iff_hasFDerivWithinAt.1 (H x hx) m
    with ⟨u, hu, -, f', p, hff', hf', Hf'⟩
  rcases mem_nhdsWithin.1 hu with ⟨o, o_open, xo, ho⟩
  rw [insert_eq_of_mem hx] at ho ⊢
  rw [inter_comm] at ho
  refine ⟨s ∩ o, inter_mem_nhdsWithin _ (o_open.mem_nhds xo), p, ?_, fun i hi ↦ (Hf' i hi).mono ho⟩
  apply (hf'.mono ho).congr (fun y hy ↦ ?_)
  have A : fderivWithin 𝕜 f (s ∩ o) y = f' y :=
    ((hff' y (ho hy)).mono ho).fderivWithin (hs.inter o_open y hy)
  rwa [fderivWithin_inter (o_open.mem_nhds hy.2)] at A

theorem contDiffOn_succ_iff_hasFDerivWithin {n : ℕ} (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 (n + 1 : ℕ) f s ↔
      ∃ f' : E → E →L[𝕜] F, ContDiffOn 𝕜 n f' s ∧ ∀ x, x ∈ s → HasFDerivWithinAt f (f' x) s x := by
  rw [contDiffOn_succ_iff_fderivWithin hs]
  refine ⟨fun h => ⟨fderivWithin 𝕜 f s, h.2, fun x hx => (h.1 x hx).hasFDerivWithinAt⟩, fun h => ?_⟩
  rcases h with ⟨f', h1, h2⟩
  refine ⟨fun x hx => (h2 x hx).differentiableWithinAt, fun x hx => ?_⟩
  exact (h1 x hx).congr' (fun y hy => (h2 y hy).fderivWithin (hs y hy)) hx

theorem contDiffOn_omega_iff_hasFDerivWithin (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 ω f s ↔
      AnalyticWithinOn 𝕜 f s ∧ ∃ f' : E → E →L[𝕜] F, ContDiffOn 𝕜 ω f' s ∧
        ∀ x, x ∈ s → HasFDerivWithinAt f (f' x) s x := by
  rw [contDiffOn_omega_iff_fderivWithin hs]
  refine ⟨fun h => ⟨h.1, fderivWithin 𝕜 f s, h.2,
    fun x hx ↦ ((h.1 x hx).differentiableWithinAt.mono (subset_insert _ _)).hasFDerivWithinAt⟩,
    fun h ↦ ?_⟩
  rcases h with ⟨hf, f', h1, h2⟩
  refine ⟨hf, ?_⟩
  apply h1.congr
  intro x hx
  exact (h2 x hx).fderivWithin (hs x hx)

/-- A function is `C^(n + 1)` on an open domain if and only if it is
differentiable there, and its derivative (expressed with `fderiv`) is `C^n`. -/
theorem contDiffOn_succ_iff_fderiv_of_isOpen {n : ℕ} (hs : IsOpen s) :
    ContDiffOn 𝕜 (n + 1 : ℕ) f s ↔
      DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 n (fun y => fderiv 𝕜 f y) s := by
  rw [contDiffOn_succ_iff_fderivWithin hs.uniqueDiffOn]
  exact Iff.rfl.and (contDiffOn_congr fun x hx ↦ fderivWithin_of_isOpen hs hx)

/-- A function is `C^∞` on a domain with unique derivatives if and only if it is differentiable
there, and its derivative (expressed with `fderivWithin`) is `C^∞`. -/
theorem contDiffOn_top_iff_fderivWithin (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 ∞ f s ↔
      DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (fun y => fderivWithin 𝕜 f s y) s := by
  constructor
  · intro h
    refine ⟨h.differentiableOn (by simp), ?_⟩
    refine contDiffOn_top.2 fun n => ((contDiffOn_succ_iff_fderivWithin hs).1 ?_).2
    apply h.of_le (WithTop.coe_le_coe.2 le_top)
  · intro h
    refine contDiffOn_top.2 fun n => ?_
    have A : (n : ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top
    apply ((contDiffOn_succ_iff_fderivWithin hs).2 ⟨h.1, h.2.of_le A⟩).of_le
    apply WithTop.coe_le_coe.2 (by simp)

/-- A function is `C^∞` on an open domain if and only if it is differentiable there, and its
derivative (expressed with `fderiv`) is `C^∞`. -/
theorem contDiffOn_top_iff_fderiv_of_isOpen (hs : IsOpen s) :
    ContDiffOn 𝕜 ∞ f s ↔ DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (fun y => fderiv 𝕜 f y) s := by
  rw [contDiffOn_top_iff_fderivWithin hs.uniqueDiffOn]
  exact Iff.rfl.and <| contDiffOn_congr fun x hx ↦ fderivWithin_of_isOpen hs hx

protected theorem ContDiffOn.fderivWithin (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hmn : m + 1 ≤ n) : ContDiffOn 𝕜 m (fderivWithin 𝕜 f s) s := by
  match n with
  | ω => exact ((contDiffOn_omega_iff_fderivWithin hs).1 hf).2.of_le le_top
  | ∞ => match m with
    | ω => simp at hmn
    | (m : ℕ∞) =>
      apply ((contDiffOn_top_iff_fderivWithin hs).1 hf).2.of_le
      exact_mod_cast le_top
  | (n : ℕ) => match m with
    | ω => simp at hmn
    | ∞ => simpa using WithTop.coe_le_coe.1 hmn
    | (m : ℕ) =>
      change (m.succ : WithTop ℕ∞) ≤ n at hmn
      exact ((contDiffOn_succ_iff_fderivWithin hs).1 (hf.of_le hmn)).2

theorem ContDiffOn.fderiv_of_isOpen (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (fun y => fderiv 𝕜 f y) s :=
  (hf.fderivWithin hs.uniqueDiffOn hmn).congr fun _ hx => (fderivWithin_of_isOpen hs hx).symm

theorem ContDiffOn.continuousOn_fderivWithin (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hn : 1 ≤ n) : ContinuousOn (fun x => fderivWithin 𝕜 f s x) s :=
  ((contDiffOn_succ_iff_fderivWithin hs).1 (h.of_le hn)).2.continuousOn

theorem ContDiffOn.continuousOn_fderiv_of_isOpen (h : ContDiffOn 𝕜 n f s) (hs : IsOpen s)
    (hn : 1 ≤ n) : ContinuousOn (fun x => fderiv 𝕜 f x) s :=
  ((contDiffOn_succ_iff_fderiv_of_isOpen hs).1 (h.of_le hn)).2.continuousOn

/-! ### Smooth functions at a point -/

variable (𝕜)

/-- A function is continuously differentiable up to `n` at a point `x` if, for any integer `k ≤ n`,
there is a neighborhood of `x` where `f` admits derivatives up to order `n`, which are continuous.
-/
def ContDiffAt (n : WithTop ℕ∞) (f : E → F) (x : E) : Prop :=
  ContDiffWithinAt 𝕜 n f univ x

variable {𝕜}

theorem contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f univ x ↔ ContDiffAt 𝕜 n f x :=
  Iff.rfl

theorem contDiffAt_top : ContDiffAt 𝕜 ∞ f x ↔ ∀ n : ℕ, ContDiffAt 𝕜 n f x := by
  simp [← contDiffWithinAt_univ, contDiffWithinAt_top]

theorem ContDiffAt.contDiffWithinAt (h : ContDiffAt 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x :=
  h.mono (subset_univ _)

theorem ContDiffWithinAt.contDiffAt (h : ContDiffWithinAt 𝕜 n f s x) (hx : s ∈ 𝓝 x) :
    ContDiffAt 𝕜 n f x := by rwa [ContDiffAt, ← contDiffWithinAt_inter hx, univ_inter]

theorem ContDiffOn.contDiffAt (h : ContDiffOn 𝕜 n f s) (hx : s ∈ 𝓝 x) :
    ContDiffAt 𝕜 n f x :=
  (h _ (mem_of_mem_nhds hx)).contDiffAt hx

theorem ContDiffAt.congr_of_eventuallyEq (h : ContDiffAt 𝕜 n f x) (hg : f₁ =ᶠ[𝓝 x] f) :
    ContDiffAt 𝕜 n f₁ x :=
  h.congr_of_eventually_eq' (by rwa [nhdsWithin_univ]) (mem_univ x)

theorem ContDiffAt.of_le (h : ContDiffAt 𝕜 n f x) (hmn : m ≤ n) : ContDiffAt 𝕜 m f x :=
  ContDiffWithinAt.of_le h hmn

theorem ContDiffAt.continuousAt (h : ContDiffAt 𝕜 n f x) : ContinuousAt f x := by
  simpa [continuousWithinAt_univ] using h.continuousWithinAt

/-- If a function is `C^n` with `n ≥ 1` at a point, then it is differentiable there. -/
theorem ContDiffAt.differentiableAt (h : ContDiffAt 𝕜 n f x) (hn : 1 ≤ n) :
    DifferentiableAt 𝕜 f x := by
  simpa [hn, differentiableWithinAt_univ] using h.differentiableWithinAt

nonrec lemma ContDiffAt.contDiffOn {m : ℕ} (h : ContDiffAt 𝕜 n f x) (hm : m ≤ n) :
    ∃ u ∈ 𝓝 x, ContDiffOn 𝕜 m f u := by
  simpa [nhdsWithin_univ] using h.contDiffOn hm

/-- A function is `C^(n + 1)` at a point iff locally, it has a derivative which is `C^n`. -/
theorem contDiffAt_succ_iff_hasFDerivAt {n : ℕ} :
    ContDiffAt 𝕜 (n + 1 : ℕ) f x ↔
      ∃ f' : E → E →L[𝕜] F, (∃ u ∈ 𝓝 x, ∀ x ∈ u, HasFDerivAt f (f' x) x) ∧ ContDiffAt 𝕜 n f' x := by
  rw [← contDiffWithinAt_univ, contDiffWithinAt_succ_iff_hasFDerivWithinAt]
  simp only [nhdsWithin_univ, exists_prop, mem_univ, insert_eq_of_mem]
  constructor
  · rintro ⟨u, H, f', h_fderiv, h_cont_diff⟩
    rcases mem_nhds_iff.mp H with ⟨t, htu, ht, hxt⟩
    refine ⟨f', ⟨t, ?_⟩, h_cont_diff.contDiffAt H⟩
    refine ⟨mem_nhds_iff.mpr ⟨t, Subset.rfl, ht, hxt⟩, ?_⟩
    intro y hyt
    refine (h_fderiv y (htu hyt)).hasFDerivAt ?_
    exact mem_nhds_iff.mpr ⟨t, htu, ht, hyt⟩
  · rintro ⟨f', ⟨u, H, h_fderiv⟩, h_cont_diff⟩
    refine ⟨u, H, f', ?_, h_cont_diff.contDiffWithinAt⟩
    intro x hxu
    exact (h_fderiv x hxu).hasFDerivWithinAt

protected theorem ContDiffAt.eventually {n : ℕ} (h : ContDiffAt 𝕜 n f x) :
    ∀ᶠ y in 𝓝 x, ContDiffAt 𝕜 n f y := by
  simpa [nhdsWithin_univ] using ContDiffWithinAt.eventually h

/-! ### Smooth functions -/

variable (𝕜)

/-- A function is continuously differentiable up to `n` if it admits derivatives up to
order `n`, which are continuous. Contrary to the case of definitions in domains (where derivatives
might not be unique) we do not need to localize the definition in space or time.
-/
def ContDiff (n : WithTop ℕ∞) (f : E → F) : Prop :=
  match n with
  | ω => ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpTo ⊤ f p
      ∧ ∀ i, AnalyticOn 𝕜 (fun x ↦ p x i) univ
  | (n : ℕ∞) => ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpTo n f p

variable {𝕜}

/-- If `f` has a Taylor series up to `n`, then it is `C^n`. -/
theorem HasFTaylorSeriesUpTo.contDiff {n : ℕ∞} {f' : E → FormalMultilinearSeries 𝕜 E F}
    (hf : HasFTaylorSeriesUpTo n f f') : ContDiff 𝕜 n f :=
  ⟨f', hf⟩

theorem contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n f := by
  match n with
  | ω =>
    constructor
    · intro H
      use ftaylorSeriesWithin 𝕜 f univ
      rw [← hasFTaylorSeriesUpToOn_univ_iff]
      refine ⟨(H.of_le (m := ∞) le_top).ftaylorSeriesWithin uniqueDiffOn_univ, fun i ↦ ?_⟩
      rw [← analyticWithinOn_univ]
      exact H.analyticWithinOn_iteratedFDerivWithin uniqueDiffOn_univ _
    · rintro ⟨p, hp, h'p⟩ x _ m
      exact ⟨univ, Filter.univ_sets _, p, (hp.hasFTaylorSeriesUpToOn univ).of_le le_top,
        fun i _ ↦ (h'p i).analyticWithinOn⟩
  | (n : ℕ∞) =>
    constructor
    · intro H
      use ftaylorSeriesWithin 𝕜 f univ
      rw [← hasFTaylorSeriesUpToOn_univ_iff]
      exact H.ftaylorSeriesWithin uniqueDiffOn_univ
    · rintro ⟨p, hp⟩ x _ m hm
      exact ⟨univ, Filter.univ_sets _, p, (hp.hasFTaylorSeriesUpToOn univ).of_le hm⟩

theorem contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ ∀ x, ContDiffAt 𝕜 n f x := by
  simp [← contDiffOn_univ, ContDiffOn, ContDiffAt]

theorem ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiffAt 𝕜 n f x :=
  contDiff_iff_contDiffAt.1 h x

theorem ContDiff.contDiffWithinAt (h : ContDiff 𝕜 n f) : ContDiffWithinAt 𝕜 n f s x :=
  h.contDiffAt.contDiffWithinAt

theorem contDiff_top : ContDiff 𝕜 ∞ f ↔ ∀ n : ℕ, ContDiff 𝕜 n f := by
  simp [contDiffOn_univ.symm, contDiffOn_top]

theorem contDiff_all_iff_nat : (∀ n : ℕ∞, ContDiff 𝕜 n f) ↔ ∀ n : ℕ, ContDiff 𝕜 n f := by
  simp only [← contDiffOn_univ, contDiffOn_all_iff_nat]

theorem ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiffOn 𝕜 n f s :=
  (contDiffOn_univ.2 h).mono (subset_univ _)

@[simp]
theorem contDiff_zero : ContDiff 𝕜 0 f ↔ Continuous f := by
  rw [← contDiffOn_univ, continuous_iff_continuousOn_univ]
  exact contDiffOn_zero

theorem contDiffAt_zero : ContDiffAt 𝕜 0 f x ↔ ∃ u ∈ 𝓝 x, ContinuousOn f u := by
  rw [← contDiffWithinAt_univ]; simp [contDiffWithinAt_zero, nhdsWithin_univ]

theorem contDiffAt_one_iff :
    ContDiffAt 𝕜 1 f x ↔
      ∃ f' : E → E →L[𝕜] F, ∃ u ∈ 𝓝 x, ContinuousOn f' u ∧ ∀ x ∈ u, HasFDerivAt f (f' x) x := by
  simp_rw [show (1 : WithTop ℕ∞) = (0 + 1 : ℕ) from (zero_add 1).symm,
    contDiffAt_succ_iff_hasFDerivAt, show ((0 : ℕ) : WithTop ℕ∞) = 0 from rfl, contDiffAt_zero,
    exists_mem_and_iff antitone_bforall antitone_continuousOn, and_comm]

theorem ContDiff.of_le (h : ContDiff 𝕜 n f) (hmn : m ≤ n) : ContDiff 𝕜 m f :=
  contDiffOn_univ.1 <| (contDiffOn_univ.2 h).of_le hmn

theorem ContDiff.of_succ {n : ℕ} (h : ContDiff 𝕜 (n + 1) f) : ContDiff 𝕜 n f :=
  h.of_le <| WithTop.coe_le_coe.mpr le_self_add

theorem ContDiff.one_of_succ {n : ℕ} (h : ContDiff 𝕜 (n + 1) f) : ContDiff 𝕜 1 f :=
  h.of_le <| WithTop.coe_le_coe.mpr le_add_self

theorem ContDiff.continuous (h : ContDiff 𝕜 n f) : Continuous f :=
  contDiff_zero.1 (h.of_le bot_le)

/-- If a function is `C^n` with `n ≥ 1`, then it is differentiable. -/
theorem ContDiff.differentiable (h : ContDiff 𝕜 n f) (hn : 1 ≤ n) : Differentiable 𝕜 f :=
  differentiableOn_univ.1 <| (contDiffOn_univ.2 h).differentiableOn hn

theorem contDiff_iff_forall_nat_le {n : ℕ∞} :
    ContDiff 𝕜 n f ↔ ∀ m : ℕ, ↑m ≤ n → ContDiff 𝕜 m f := by
  simp_rw [← contDiffOn_univ]; exact contDiffOn_iff_forall_nat_le

/-- A function is `C^(n+1)` iff it has a `C^n` derivative. -/
theorem contDiff_succ_iff_hasFDerivAt {n : ℕ} :
    ContDiff 𝕜 (n + 1 : ℕ) f ↔
      ∃ f' : E → E →L[𝕜] F, ContDiff 𝕜 n f' ∧ ∀ x, HasFDerivAt f (f' x) x := by
  simp only [← contDiffOn_univ, ← hasFDerivWithinAt_univ,
    contDiffOn_succ_iff_hasFDerivWithin uniqueDiffOn_univ, Set.mem_univ, forall_true_left]

theorem contDiff_one_iff_hasFDerivAt : ContDiff 𝕜 1 f ↔
    ∃ f' : E → E →L[𝕜] F, Continuous f' ∧ ∀ x, HasFDerivAt f (f' x) x := by
  convert contDiff_succ_iff_hasFDerivAt using 4; simp

theorem contDiff_of_analyticOn_of_fderiv (hf : AnalyticOn 𝕜 f univ)
    (h : ContDiff 𝕜 ω (fun y ↦ fderiv 𝕜 f y)) : ContDiff 𝕜 n f := by
  rw [← contDiffOn_univ] at h ⊢
  apply contDiffOn_of_analyticWithinOn_of_fderivWithin
  · simpa using hf
  · simpa [fderivWithin_univ] using h

/-! ### Iterated derivative -/


/-- When a function is `C^n` in a set `s` of unique differentiability, it admits
`ftaylorSeriesWithin 𝕜 f s` as a Taylor series up to order `n` in `s`. -/
theorem contDiff_iff_ftaylorSeries {n : ℕ∞} :
    ContDiff 𝕜 n f ↔ HasFTaylorSeriesUpTo n f (ftaylorSeries 𝕜 f) := by
  constructor
  · rw [← contDiffOn_univ, ← hasFTaylorSeriesUpToOn_univ_iff, ← ftaylorSeriesWithin_univ]
    exact fun h => ContDiffOn.ftaylorSeriesWithin h uniqueDiffOn_univ
  · intro h; exact ⟨ftaylorSeries 𝕜 f, h⟩

theorem contDiff_iff_continuous_differentiable {n : ℕ∞} :
    ContDiff 𝕜 n f ↔
      (∀ m : ℕ, (m : ℕ∞) ≤ n → Continuous fun x => iteratedFDeriv 𝕜 m f x) ∧
        ∀ m : ℕ, (m : ℕ∞) < n → Differentiable 𝕜 fun x => iteratedFDeriv 𝕜 m f x := by
  simp [contDiffOn_univ.symm, continuous_iff_continuousOn_univ, differentiableOn_univ.symm,
    iteratedFDerivWithin_univ, contDiffOn_iff_continuousOn_differentiableOn uniqueDiffOn_univ]

theorem contDiff_omega_iff_analyticOn_iteratedFDeriv :
    ContDiff 𝕜 ω f ↔ ∀ m, AnalyticOn 𝕜 (iteratedFDeriv 𝕜 m f) univ := by
  simp_rw [← contDiffOn_univ, ← analyticWithinOn_univ,
    contDiffOn_omega_iff_analyticWithinOn_iteratedFDerivWithin uniqueDiffOn_univ,
    iteratedFDerivWithin_univ]

theorem contDiff_of_analyticOn_iteratedFDeriv
    (h : ∀ m, AnalyticOn 𝕜 (iteratedFDeriv 𝕜 m f) univ) : ContDiff 𝕜 n f :=
  (contDiff_omega_iff_analyticOn_iteratedFDeriv.2 h).of_le le_top

/-- If `f` is `C^n` then its `m`-times iterated derivative is continuous for `m ≤ n`. -/
theorem ContDiff.continuous_iteratedFDeriv {m : ℕ} (hm : (m : ℕ∞) ≤ n) (hf : ContDiff 𝕜 n f) :
    Continuous fun x => iteratedFDeriv 𝕜 m f x :=
  (contDiff_iff_continuous_differentiable.1 (hf.of_le hm)).1 m le_rfl

/-- If `f` is `C^n` then its `m`-times iterated derivative is differentiable for `m < n`. -/
theorem ContDiff.differentiable_iteratedFDeriv {m : ℕ} (hm : (m : ℕ∞) < n) (hf : ContDiff 𝕜 n f) :
    Differentiable 𝕜 fun x => iteratedFDeriv 𝕜 m f x :=
  (contDiff_iff_continuous_differentiable.mp (hf.of_le (ENat.add_one_nat_le_withTop_of_lt hm))).2 m
    (by exact_mod_cast lt_add_one m)

theorem contDiff_of_differentiable_iteratedFDeriv {n : ℕ∞}
    (h : ∀ m : ℕ, (m : ℕ∞) ≤ n → Differentiable 𝕜 (iteratedFDeriv 𝕜 m f)) : ContDiff 𝕜 n f :=
  contDiff_iff_continuous_differentiable.2
    ⟨fun m hm => (h m hm).continuous, fun m hm => h m (le_of_lt hm)⟩

/-- A function is `C^(n + 1)` if and only if it is differentiable,
and its derivative (formulated in terms of `fderiv`) is `C^n`. -/
theorem contDiff_succ_iff_fderiv {n : ℕ} :
    ContDiff 𝕜 (n + 1 : ℕ) f ↔ Differentiable 𝕜 f ∧ ContDiff 𝕜 n fun y => fderiv 𝕜 f y := by
  simp only [← contDiffOn_univ, ← differentiableOn_univ, ← fderivWithin_univ,
    contDiffOn_succ_iff_fderivWithin uniqueDiffOn_univ]

theorem contDiff_one_iff_fderiv : ContDiff 𝕜 1 f ↔ Differentiable 𝕜 f ∧ Continuous (fderiv 𝕜 f) :=
  contDiff_succ_iff_fderiv.trans <| Iff.rfl.and contDiff_zero

/-- A function is `C^∞` if and only if it is differentiable,
and its derivative (formulated in terms of `fderiv`) is `C^∞`. -/
theorem contDiff_top_iff_fderiv :
    ContDiff 𝕜 ∞ f ↔ Differentiable 𝕜 f ∧ ContDiff 𝕜 ∞ fun y => fderiv 𝕜 f y := by
  simp only [← contDiffOn_univ, ← differentiableOn_univ, ← fderivWithin_univ]
  rw [contDiffOn_top_iff_fderivWithin uniqueDiffOn_univ]

theorem ContDiff.continuous_fderiv (h : ContDiff 𝕜 n f) (hn : 1 ≤ n) :
    Continuous fun x => fderiv 𝕜 f x :=
  (contDiff_succ_iff_fderiv.1 (h.of_le hn)).2.continuous

/-- If a function is at least `C^1`, its bundled derivative (mapping `(x, v)` to `Df(x) v`) is
continuous. -/
theorem ContDiff.continuous_fderiv_apply (h : ContDiff 𝕜 n f) (hn : 1 ≤ n) :
    Continuous fun p : E × E => (fderiv 𝕜 f p.1 : E → F) p.2 :=
  have A : Continuous fun q : (E →L[𝕜] F) × E => q.1 q.2 := isBoundedBilinearMap_apply.continuous
  have B : Continuous fun p : E × E => (fderiv 𝕜 f p.1, p.2) :=
    ((h.continuous_fderiv hn).comp continuous_fst).prod_mk continuous_snd
  A.comp B
