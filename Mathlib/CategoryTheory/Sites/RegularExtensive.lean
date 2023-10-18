/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct
import Mathlib.CategoryTheory.Sites.Coherent
import Mathlib.Tactic.ApplyFun
/-!

# The Regular and Extensive Coverages

This file defines two coverages on a category `C`.

The first one is called the *regular* coverage and for that to exist, the category `C` must satisfy
a condition called `Preregular C`. This means that effective epimorphisms can be "pulled back". The
covering sieves of this coverage are generated by presieves consisting of a single effective
epimorphism.

The second one is called the *extensive* coverage and for that to exist, the category `C` must
satisfy a condition called `Extensive C`. This means `C` has finite coproducts and that those
are preserved by pullbacks. The covering sieves of this coverage are generated by presieves
consisting finitely many arrows that together induce an isomorphism from the coproduct to the
target.

In `extensive_union_regular_generates_coherent`, we prove that the union of these two coverages
generates the coherent topology on `C` if `C` is precoherent, extensive and regular.

In `isSheafFor_extensive_of_preservesFiniteProducts`, we prove that a finite product preserving
presheaf satisfies the sheaf condition for a sieve consiting of finitely many arrows that together
induce an isomorphism from the coproduct of their sources.

TODO: figure out under what conditions `Preregular` and `Extensive` are implied by `Precoherent` and
vice versa.

-/

universe v u w

namespace CategoryTheory

open Limits

variable (C : Type u) [Category.{v} C]

/--
The condition `Preregular C` is property that effective epis can be "pulled back" along any
morphism. This is satisfied e.g. by categories that have pullbacks that preserve effective
epimorphisms (like `Profinite` and `CompHaus`), and categories where every object is projective
(like  `Stonean`).
-/
class Preregular : Prop where
  /--
  For `X`, `Y`, `Z`, `f`, `g` like in the diagram, where `g` is an effective epi, there exists
  an object `W`, an effective epi `h : W ⟶ X` and a morphism `i : W ⟶ Z` making the diagram
  commute.
  ```
  W --i-→ Z
  |       |
  h       g
  ↓       ↓
  X --f-→ Y
  ```
  -/
  exists_fac : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y) [EffectiveEpi g],
    (∃ (W : C) (h : W ⟶ X) (_ : EffectiveEpi h) (i : W ⟶ Z), i ≫ g = h ≫ f)

/--
Describes the property of having pullbacks of morphsims into a finite coproduct, where one
of the morphisms is an inclusion map into the coproduct (up to isomorphism).
-/
class HasPullbacksOfInclusions : Prop where
    /-- For any morphism `f : X ⟶ Z`, where `Z` is the coproduct of `i : (a : α) → Y a ⟶ Z` with
    `α` finite, the pullback of `f` and `i a` exists for every `a : α`. -/
    has_pullback : ∀ {X Z : C} {α : Type w} (f : X ⟶ Z) {Y : (a : α) → C}
    (i : (a : α) → Y a ⟶ Z) [Fintype α] [HasCoproduct Y] [IsIso (Sigma.desc i)] (a : α),
    HasPullback f (i a)

instance [HasPullbacksOfInclusions C] {X Z : C} {α : Type w} (f : X ⟶ Z) {Y : (a : α) → C}
    (i : (a : α) → Y a ⟶ Z) [Fintype α] [HasCoproduct Y] [IsIso (Sigma.desc i)] (a : α) :
    HasPullback f (i a) := HasPullbacksOfInclusions.has_pullback f i a

/--
If `C` has pullbacks then it has the pullbacks relevant to `HasPullbacksOfInclusions`.
-/
instance (priority := 10) [HasPullbacks C] :
  HasPullbacksOfInclusions C := ⟨fun _ _ _ => inferInstance⟩

/--
A category is *extensive* if it has all finite coproducts and those coproducts are preserved
by pullbacks (we only require the relevant pullbacks to exist, via `HasPullbacksOfInclusions`).

TODO: relate this to the class `FinitaryExtensive`
-/
class Preextensive extends HasFiniteCoproducts C, HasPullbacksOfInclusions C : Prop where
  /-- Pulling back an isomorphism from a coproduct yields an isomorphism. -/
  sigma_desc_iso : ∀ {α : Type} [Fintype α] {X : C} {Z : α → C} (π : (a : α) → Z a ⟶ X)
    {Y : C} (f : Y ⟶ X) (_ : IsIso (Sigma.desc π)),
    IsIso (Sigma.desc ((fun _ ↦ pullback.fst) : (a : α) → pullback f (π a) ⟶ _))

class Extensive extends Preextensive C, CoproductsDisjoint C

/--
The regular coverage on a regular category `C`.
-/
def regularCoverage [Preregular C] : Coverage C where
  covering B := { S | ∃ (X : C) (f : X ⟶ B), S = Presieve.ofArrows (fun (_ : Unit) ↦ X)
    (fun (_ : Unit) ↦ f) ∧ EffectiveEpi f }
  pullback := by
    intro X Y f S ⟨Z, π, hπ, h_epi⟩
    have := Preregular.exists_fac f π
    obtain ⟨W, h, _, i, this⟩ := this
    refine ⟨Presieve.singleton h, ⟨?_, ?_⟩⟩
    · exact ⟨W, h, by {rw [Presieve.ofArrows_pUnit h]}, inferInstance⟩
    · intro W g hg
      cases hg
      refine ⟨Z, i, π, ⟨?_, this⟩⟩
      cases hπ
      rw [Presieve.ofArrows_pUnit]
      exact Presieve.singleton.mk

/--
The extensive coverage on an extensive category `C`
-/
def extensiveCoverage [Preextensive C] : Coverage C where
  covering B := { S | ∃ (α : Type) (_ : Fintype α) (X : α → C) (π : (a : α) → (X a ⟶ B)),
    S = Presieve.ofArrows X π ∧ IsIso (Sigma.desc π) }
  pullback := by
    intro X Y f S ⟨α, hα, Z, π, hS, h_iso⟩
    let Z' : α → C := fun a ↦ pullback f (π a)
    let π' : (a : α) → Z' a ⟶ Y := fun a ↦ pullback.fst
    refine ⟨@Presieve.ofArrows C _ _ α Z' π', ⟨?_, ?_⟩⟩
    · constructor
      exact ⟨hα, Z', π', ⟨by simp only, Preextensive.sigma_desc_iso (fun x => π x) f h_iso⟩⟩
    · intro W g hg
      rcases hg with ⟨a⟩
      refine ⟨Z a, pullback.snd, π a, ?_, by rw [CategoryTheory.Limits.pullback.condition]⟩
      rw [hS]
      refine Presieve.ofArrows.mk a


/-- The union of the extensive and regular coverages generates the coherent topology on `C`. -/
lemma extensive_regular_generate_coherent [Preregular C] [Preextensive C] [Precoherent C] :
    ((extensiveCoverage C) ⊔ (regularCoverage C)).toGrothendieck =
    (coherentTopology C) := by
  ext B S
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · induction h with
    | of Y T hT =>
      apply Coverage.saturate.of
      simp only [Coverage.sup_covering, Set.mem_union] at hT
      exact Or.elim hT
        (fun ⟨α, x, X, π, ⟨h, _⟩⟩ ↦ ⟨α, x, X, π, ⟨h, inferInstance⟩⟩)
        (fun ⟨Z, f, ⟨h, _⟩⟩ ↦ ⟨Unit, inferInstance, fun _ ↦ Z, fun _ ↦ f, ⟨h, inferInstance⟩⟩)
    | top => apply Coverage.saturate.top
    | transitive Y T => apply Coverage.saturate.transitive Y T<;> [assumption; assumption]
  · induction h with
    | of Y T hT =>
      obtain ⟨I, hI, X, f, ⟨h, hT⟩⟩ := hT
      let φ := fun (i : I) ↦ Sigma.ι X i
      let F := Sigma.desc f
      let Z := Sieve.generate T
      let Xs := (∐ fun (i : I) => X i)
      let Zf := Sieve.generate (Presieve.ofArrows (fun (_ : Unit) ↦ Xs) (fun (_ : Unit) ↦ F))
      apply Coverage.saturate.transitive Y Zf
      · apply Coverage.saturate.of
        simp only [Coverage.sup_covering, extensiveCoverage, regularCoverage, Set.mem_union,
          Set.mem_setOf_eq]
        exact Or.inr ⟨Xs, F, ⟨rfl, inferInstance⟩⟩
      · intro R g hZfg
        dsimp at hZfg
        rw [Presieve.ofArrows_pUnit] at hZfg
        obtain ⟨W, ψ, σ, ⟨hW, hW'⟩⟩ := hZfg
        induction hW
        rw [← hW', Sieve.pullback_comp Z]
        suffices Sieve.pullback ψ ((Sieve.pullback F) Z) ∈ GrothendieckTopology.sieves
          ((extensiveCoverage C) ⊔ (regularCoverage C)).toGrothendieck R by assumption
        apply GrothendieckTopology.pullback_stable'
        suffices Coverage.saturate ((extensiveCoverage C) ⊔ (regularCoverage C)) Xs
          (Z.pullback F) by assumption
        suffices : Sieve.generate (Presieve.ofArrows X φ) ≤ Z.pullback F
        · apply Coverage.saturate_of_superset _ this
          apply Coverage.saturate.of
          simp only [Coverage.sup_covering, extensiveCoverage, regularCoverage, Set.mem_union,
            Set.mem_setOf_eq]
          refine Or.inl ⟨I, hI, X, φ, ⟨rfl, ?_⟩⟩
          suffices Sigma.desc φ = 𝟙 _ by rw [this]; infer_instance
          ext
          simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, Category.comp_id]
        intro Q q hq
        simp only [Sieve.pullback_apply, Sieve.generate_apply]
        simp only [Sieve.generate_apply] at hq
        obtain ⟨E, e, r, hq⟩ := hq
        refine' ⟨E, e, r ≫ F, ⟨_, _⟩⟩
        · rw [h]
          induction hq.1
          simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
          exact Presieve.ofArrows.mk _
        · rw [← hq.2]
          simp only [Category.assoc]
    | top => apply Coverage.saturate.top
    | transitive Y T => apply Coverage.saturate.transitive Y T<;> [assumption; assumption]

section ExtensiveSheaves

variable [Preextensive C] {C}

/-- A presieve is *extensive* if it is finite and its arrows induce an isomorphism from the
coproduct to the target. -/
class Presieve.extensive [HasFiniteCoproducts C] {X : C} (R : Presieve X) :
    Prop where
  /-- `R` consists of a finite collection of arrows that together induce an isomorphism from the
  coproduct of their sources. -/
  arrows_sigma_desc_iso : ∃ (α : Type) (_ : Fintype α) (Z : α → C) (π : (a : α) → (Z a ⟶ X)),
    R = Presieve.ofArrows Z π ∧ IsIso (Sigma.desc π)

instance {X : C} (S : Presieve X) [S.extensive] : S.hasPullbacks where
  has_pullbacks := by
    obtain ⟨_, _, _, _, hS, _⟩ := Presieve.extensive.arrows_sigma_desc_iso (R := S)
    intro _ _ f hf _ hg
    rw [hS] at hf hg
    cases' hg with b
    apply HasPullbacksOfInclusions.has_pullback f

namespace ExtensiveSheafConditionProof

lemma sigma_surjective {α : Type} {Z : α → C} {X : C} (π : (a : α) → Z a ⟶ X) :
    Function.Surjective (fun a => ⟨Z a, π a, Presieve.ofArrows.mk a⟩ :
    α → Σ(Y : C), { f : Y ⟶ X // Presieve.ofArrows Z π f }) :=
  fun ⟨_, ⟨_, hf⟩⟩ ↦ by cases' hf with a _; exact ⟨a, rfl⟩

-- noncomputable
-- def map {α : Type} {Z : α → C} {X : C} (π : (a : α) → Z a ⟶ X) :
--     (Σ(Y : C), { f : Y ⟶ X // Presieve.ofArrows Z π f }) → α :=
--   Function.surjInv (sigma_surjective π)

-- def map2 {α : Type} {Z : α → C} {X : C} (π : (a : α) → Z a ⟶ X)
--     (f : Σ(Y : C), { f : Y ⟶ X // Presieve.ofArrows Z π f }) :
--     f.fst ⟶ Z (map π f) := sorry

lemma map_eq {α : Type} {Z : α → C} {X : C} (π : (a : α) → Z a ⟶ X)
    (f : Σ(Y : C), { f : Y ⟶ X // Presieve.ofArrows Z π f }) :
    ∃ i, f.fst = Z i := by
  obtain ⟨Y, g, h⟩ := f
  cases' h with i
  exact ⟨i, rfl⟩

open Opposite

instance {α : Type} {Z : α → C} {X : C} {π : (a : α) → Z a ⟶ X} [Fintype α] :
    HasProduct fun (x : Σ(Y : C), { f : Y ⟶ X // Presieve.ofArrows Z π f }) ↦ (op x.1) :=
  haveI := Finite.of_surjective _ (sigma_surjective.{v, u} π)
  inferInstance

/-- The canonical map from `Equalizer.FirstObj` to a product indexed by `α` -/
noncomputable
def prod_map {α : Type} {Z : α → C} {X : C} (π : (a : α) → Z a ⟶ X) (F : Cᵒᵖ ⥤ Type max u v) :
    (∏ fun (f : (Σ(Y : C), { f : Y ⟶ X // Presieve.ofArrows Z π f })) => F.obj (op f.fst)) ⟶
    ∏ fun a => F.obj (op (Z a)) :=
  Pi.lift (fun a => Pi.π (fun (f : (Σ(Y : C), { f : Y ⟶ X // Presieve.ofArrows Z π f })) =>
    F.obj (op f.fst)) ⟨Z a, π a, Presieve.ofArrows.mk a⟩)

noncomputable
def prod_map' {α : Type} {Z : α → C} {X : C} (π : (a : α) → Z a ⟶ X) (F : Cᵒᵖ ⥤ Type max u v) :
    (∏ fun (f : (Σ(Y : C), { f : Y ⟶ X // Presieve.ofArrows Z π f })) => F.obj (op f.fst)) ⟶
    ∏ fun a => F.obj (op (Z a)) :=
  Pi.map' (fun a => ⟨Z a, π a, Presieve.ofArrows.mk a⟩) (fun _ ↦ F.map (𝟙 _))

/-- The canonical map from `Equalizer.FirstObj` to a product indexed by `α` -/
noncomputable
def prod_map_inv' {α : Type} {Z : α → C} {X : C} (π : (a : α) → Z a ⟶ X) (F : Cᵒᵖ ⥤ Type max u v) :
     (∏ fun a => F.obj (op (Z a))) ⟶
    (∏ fun (f : (Σ(Y : C), { f : Y ⟶ X // Presieve.ofArrows Z π f })) => F.obj (op f.fst)) :=
  Pi.map' (fun f ↦ (map_eq π f).choose) (fun f ↦ F.map (eqToHom (map_eq π f).choose_spec).op)

/-- The canonical map from `Equalizer.FirstObj` to a product indexed by `α` -/
noncomputable
def prod_map_inv {α : Type} {Z : α → C} {X : C} (π : (a : α) → Z a ⟶ X) (F : Cᵒᵖ ⥤ Type max u v) :
     (∏ fun a => F.obj (op (Z a))) ⟶
    (∏ fun (f : (Σ(Y : C), { f : Y ⟶ X // Presieve.ofArrows Z π f })) => F.obj (op f.fst)) :=
  Pi.lift (fun f ↦ (Pi.π (fun a => F.obj (op (Z a))) (map_eq π f).choose ≫
    F.map (eqToHom (map_eq π f).choose_spec).op))

/-- The inverse to `Equalizer.forkMap F (Presieve.ofArrows Z π)`. -/
noncomputable
def firstObj_to_base {α : Type} [Fintype α] {Z : α → C} {X : C} (π : (a : α) → Z a ⟶ X)
    (F : Cᵒᵖ ⥤ Type max u v) [PreservesFiniteProducts F] [IsIso (Sigma.desc π)] :
    Equalizer.FirstObj F (Presieve.ofArrows Z π) ⟶ F.obj (op X) :=
  haveI : PreservesLimit (Discrete.functor fun a => op (Z a)) F :=
    (PreservesFiniteProducts.preserves α).preservesLimit
  (prod_map π F) ≫ ((Limits.PreservesProduct.iso F (fun a => op <| Z a)).inv ≫
    F.map (opCoproductIsoProduct Z).inv ≫ F.map (inv (Sigma.desc π).op))

lemma comp_inv_desc_eq_ι {α : Type} [Fintype α] {Z : α → C} {X : C} (π : (a : α) → Z a ⟶ X)
    [IsIso (Sigma.desc π)] (a : α) : π a ≫ inv (Sigma.desc π) = Sigma.ι _ a := by
  simp only [IsIso.comp_inv_eq, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]

@[simp]
lemma PreservesProduct.isoInvCompMap {C : Type u} [Category C] {D : Type v} [Category D] (F : C ⥤ D)
    {J : Type w} {f : J → C} [HasProduct f] [HasProduct (fun j => F.obj (f j))]
    [PreservesLimit (Discrete.functor f) F] (j : J) :
    (PreservesProduct.iso F f).inv ≫ F.map (Pi.π _ j) = Pi.π _ j :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) (⟨j⟩ : Discrete J)

instance {α : Type} [Fintype α] {Z : α → C} {F : C ⥤ Type w}
    [PreservesFiniteProducts F] : PreservesLimit (Discrete.functor fun a => (Z a)) F :=
  (PreservesFiniteProducts.preserves α).preservesLimit

instance {X : C} (S : Presieve X) [S.extensive]
    {F : Cᵒᵖ ⥤ Type max u v} [PreservesFiniteProducts F] : IsIso (Equalizer.forkMap F S) := by
  obtain ⟨α, _, Z, π, hS, _⟩ := Presieve.extensive.arrows_sigma_desc_iso (R := S)
  subst hS
  refine' ⟨firstObj_to_base π F,_,_⟩
  · simp only [firstObj_to_base, ← Category.assoc, Functor.map_inv,
      IsIso.comp_inv_eq, Category.id_comp, ← Functor.mapIso_inv, Iso.comp_inv_eq,
      Functor.mapIso_hom, Iso.comp_inv_eq, ← Functor.map_comp,
      desc_op_comp_opCoproductIsoProduct_hom, PreservesProduct.iso_hom, map_lift_piComparison,
      colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    funext s
    ext a
    simp only [prod_map, types_comp_apply, Types.Limit.lift_π_apply, Fan.mk_pt, Fan.mk_π_app,
      Equalizer.forkMap, Types.pi_lift_π_apply]
  · refine Limits.Pi.hom_ext _ _ (fun f => ?_)
    simp only [Equalizer.forkMap, Category.assoc, limit.lift_π, Fan.mk_pt, Fan.mk_π_app,
      Category.id_comp]
    obtain ⟨a, ha⟩ := sigma_surjective π f
    rw [firstObj_to_base, Category.assoc, Category.assoc, Category.assoc, ← Functor.map_comp,
      ← op_inv, ← op_comp, ← ha, comp_inv_desc_eq_ι, ← Functor.map_comp,
      opCoproductIsoProduct_inv_comp_ι, PreservesProduct.isoInvCompMap F a]
    simp only [prod_map, limit.lift_π, Fan.mk_pt, Fan.mk_π_app]

end ExtensiveSheafConditionProof

open ExtensiveSheafConditionProof

lemma isSheafFor_extensive_of_preservesFiniteProducts {X : C} (S : Presieve X) [S.extensive]
    (F : Cᵒᵖ ⥤ Type max u v) [PreservesFiniteProducts F] :
    Presieve.IsSheafFor F S := by
  refine' (Equalizer.Presieve.sheaf_condition F S).2 _
  rw [Limits.Types.type_equalizer_iff_unique]
  suffices : IsIso (Equalizer.forkMap F S)
  · intro y _
    refine' ⟨inv (Equalizer.forkMap F S) y, _, fun y₁ hy₁ => _⟩
    · change (inv (Equalizer.forkMap F S) ≫ (Equalizer.forkMap F S)) y = y
      rw [IsIso.inv_hom_id, types_id_apply]
    · replace hy₁ := congr_arg (inv (Equalizer.forkMap F S)) hy₁
      change ((Equalizer.forkMap F S) ≫ inv (Equalizer.forkMap F S)) _ = _ at hy₁
      rwa [IsIso.hom_inv_id, types_id_apply] at hy₁
  infer_instance

namespace ExtensiveSheafConditionProof

open Opposite

variable {α : Type} [Fintype α] (Z : α → C) (F : Cᵒᵖ ⥤ Type max u v)
    (hF : Presieve.IsSheafFor F (Presieve.ofArrows Z (fun j ↦ Sigma.ι Z j)))

-- instance : (Presieve.ofArrows Z (fun j ↦ Sigma.ι Z j)).hasPullbacks := sorry

instance : (Presieve.ofArrows Z (fun j ↦ Sigma.ι Z j)).extensive := sorry

lemma sigma_injective [Extensive C] : Function.Injective (fun a => ⟨Z a, (fun j ↦ Sigma.ι Z j) a,
    Presieve.ofArrows.mk a⟩ : α → Σ(Y : C), { f : Y ⟶ _ //
    Presieve.ofArrows Z (fun j ↦ Sigma.ι Z j) f }) := by
  intro a b h
  simp only [Sigma.mk.inj_iff] at h
  by_contra hh
  rw [and_iff_not_or_not] at h
  apply h
  sorry

lemma eq_comp_of_heq {X Y Z W : C} (h : Y = Z) (f : Y ⟶ W) (g : Z ⟶ W) (i : X ⟶ Y) (j : X ⟶ Z)
    (hfg : HEq f g) (hij : i = j ≫ eqToHom h.symm) : i ≫ f = j ≫ g := by
  cases h; cases hfg; cases hij; simp only [eqToHom_refl, Category.comp_id]

lemma heq_of_eq_comp {X Y Z : C} (h : Y = Z) (f : X ⟶ Y) (g : X ⟶ Z) (hfg : f ≫ eqToHom h = g) :
    HEq f g := by
  cases h; cases hfg; simp only [eqToHom_refl, Category.comp_id, heq_eq_eq]


lemma prod_map_inj : Function.Injective (prod_map (fun j ↦ Sigma.ι Z j) F) := by
  intro a b h
  ext ⟨f⟩
  obtain ⟨c, hc⟩ := sigma_surjective (fun j ↦ Sigma.ι Z j) f
  subst hc
  apply_fun Pi.π (fun i ↦ F.obj (op (Z i))) c at h
  simp only [prod_map, Types.pi_lift_π_apply] at h
  exact h

-- ⟨f⟩ : Discrete (Σ(Y : C), { φ : Y ⟶ ∐ Z // Presieve.ofArrows Z (fun j ↦ Sigma.ι Z j) φ })

lemma prod_map_surj : Function.Surjective (prod_map (fun j ↦ Sigma.ι Z j) F) := by
  intro a
  let g := fun f ↦ (Pi.π (fun a ↦ F.obj (op (Z a))) (map_eq (fun j ↦ Sigma.ι Z j) f).choose ≫
    F.map (eqToHom (map_eq (fun j ↦ Sigma.ι Z j) f).choose_spec).op) a
  refine ⟨Types.Limit.mk (Discrete.functor (fun (f : (Σ(Y : C), { f : Y ⟶ _ //
      Presieve.ofArrows Z (fun j ↦ Sigma.ι Z j) f })) ↦ F.obj (op f.fst))) (fun f ↦ g f.1) ?_, ?_⟩
  · intro ⟨j⟩ ⟨k⟩ f
    cases Discrete.eq_of_hom f
    rfl
  · ext ⟨j⟩
    simp only [Discrete.functor_obj, prod_map, eqToHom_op, types_comp_apply, Types.pi_lift_π_apply,
      Types.Limit.π_mk, Pi.π]
    have : ∀ b, limit.π (Discrete.functor (fun a ↦ F.obj (op (Z a)))) b =
        Pi.π (fun a ↦ F.obj (op (Z a))) b.1 := by intros; rfl
    rw [this, this]
    dsimp
    have h := map_eq (fun j ↦ Sigma.ι Z j)
    sorry

lemma prod_map_inv_inj : Function.Injective (prod_map_inv (fun j ↦ Sigma.ι Z j) F) := by
  intro a b h
  ext ⟨j⟩
  simp only [prod_map_inv, eqToHom_op] at h
  sorry

lemma prod_map_inv_surj : Function.Injective (prod_map_inv (fun j ↦ Sigma.ι Z j) F) := sorry

lemma prod_map_comp_inv :
    prod_map' (fun j ↦ Sigma.ι Z j) F ≫ prod_map_inv' (fun j ↦ Sigma.ι Z j) F = 𝟙 _ := by
  simp only [prod_map', Functor.map_id, prod_map_inv', eqToHom_op]
  rw [Pi.map'_comp_map', ← Pi.map'_id_id]
  refine Pi.map'_eq ?_ ?_
  · funext x
    simp only [Function.comp_apply, id_eq]
    sorry
  · intro b; ext; simp; sorry

lemma prod_map_inv_comp :
    prod_map_inv' (fun j ↦ Sigma.ι Z j) F ≫ prod_map' (fun j ↦ Sigma.ι Z j) F  = 𝟙 _ := by
  simp only [prod_map_inv', eqToHom_op, prod_map', Functor.map_id]
  rw [Pi.map'_comp_map', ← Pi.map'_id_id]
  refine Pi.map'_eq ?_ ?_
  · ext x; simp only [Function.comp_apply, id_eq]; sorry
  · intro b; ext; simp; sorry

lemma one : F.map (opCoproductIsoProduct Z).inv ≫
    Equalizer.forkMap F (Presieve.ofArrows Z (fun j ↦ Sigma.ι Z j)) ≫ prod_map _ F =
    piComparison F (fun z ↦ op (Z z)) := by
  have : (Equalizer.forkMap F (Presieve.ofArrows Z (fun j ↦ Sigma.ι Z j)) ≫
      prod_map (fun j ↦ Sigma.ι Z j) F) = Pi.lift (fun j ↦ F.map ((fun j ↦ Sigma.ι Z j) j).op) := by
    ext; simp [prod_map, Equalizer.forkMap]
  rw [this]
  have t : Pi.lift (fun j ↦ Pi.π (fun a ↦ (op (Z a))) j) = 𝟙 _ := by ext; simp -- why not just simp?
  have hh : (fun j ↦ (opCoproductIsoProduct Z).inv ≫ (Sigma.ι Z j).op) =
      fun j ↦ Pi.π (fun a ↦ (op (Z a))) j
  · ext j
    exact opCoproductIsoProduct_inv_comp_ι _ _
  have : F.map (Pi.lift (fun j ↦ (opCoproductIsoProduct Z).inv ≫ (Sigma.ι Z j).op)) ≫
      piComparison F (fun z ↦ op (Z z)) =
      (F.map (opCoproductIsoProduct Z).inv ≫ Pi.lift fun j ↦ F.map ((fun j ↦ Sigma.ι Z j) j).op)
  · rw [hh, t]
    ext j x
    simp only [Functor.map_id, Category.id_comp, piComparison, types_comp_apply,
      Types.pi_lift_π_apply, ← FunctorToTypes.map_comp_apply, congr_fun hh j]
  rw [← this, hh]
  congr
  ext
  simp [t]

lemma two : Equalizer.Presieve.firstMap F (Presieve.ofArrows Z (fun j ↦ Sigma.ι Z j)) =
    Equalizer.Presieve.secondMap F (Presieve.ofArrows Z (fun j ↦ Sigma.ι Z j)) := by
  ext a
  simp only [Equalizer.Presieve.SecondObj, Equalizer.Presieve.firstMap,
    Equalizer.Presieve.secondMap]
  ext ⟨j⟩
  simp only [Discrete.functor_obj, Types.pi_lift_π_apply, types_comp_apply]
  obtain ⟨⟨j1, f1, h1⟩, ⟨j2, f2, h2⟩⟩ := j
  cases' h1 with i1
  cases' h2 with i2
  by_cases hi : i1 = i2
  · rw [hi]
    sorry
  · sorry


end ExtensiveSheafConditionProof

open Opposite

noncomputable
instance (F : Cᵒᵖ ⥤ Type max u v) (h : ∀ {X : C} (S : Presieve X) [S.extensive], S.IsSheafFor F) :
    PreservesFiniteProducts F := by
  constructor
  intro J _
  constructor
  intro K
  let k : J → Cᵒᵖ := fun j ↦ K.obj ⟨j⟩
  let i : K ≅ (Discrete.functor k) := Discrete.natIsoFunctor
  let S := (Presieve.ofArrows (fun j ↦ unop (k j)) (fun j ↦ Sigma.ι (fun j ↦ unop (k j)) j))
  specialize h S
  refine @preservesLimitOfIsoDiagram _ _ _ _ _ _ _ _ F i.symm ?_
  refine @PreservesProduct.ofIsoComparison _ _ _ _ F _ k _ _ ?_
  have hh : piComparison F (fun j ↦ op (unop (k j))) = piComparison F k := rfl
  rw [← hh]
  rw [(one (fun j ↦ (k j).unop) F).symm]
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance ?_
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ ?_ ?_
  · rw [isIso_iff_bijective, Function.bijective_iff_existsUnique]
    rw [Equalizer.Presieve.sheaf_condition, Limits.Types.type_equalizer_iff_unique] at h
    exact fun b ↦ h b (congr_fun (two (fun j ↦ unop (k j)) F) b)
  · sorry
    -- refine Limits.Pi.hom_ext _ _ (fun f => ?_)

    -- rw [isIso_iff_bijective]
    -- refine ⟨fun a b hab ↦ ?_, fun a ↦ ?_⟩
    -- · ext Y f hf
    --   cases' hf with i
    --   simp only [prod_map, op_unop] at hab
    --   sorry
    -- · refine ⟨prod_map_inv _ _ a, ?_⟩
    --   ext j
    --   sorry

    -- refine ⟨prod_map_inv _ _, ?_, ?_⟩
    -- · -- simp only [prod_map, op_unop, Category.comp_id, prod_map_inv, eqToHom_op]
    --   ext a Y f hf
    --   cases' hf with i
    --   dsimp only [prod_map_inv, prod_map]
    --   simp only [op_unop, eqToHom_op, types_comp_apply, Types.pi_lift_π_apply, types_id_apply]
    --   sorry
    -- · simp only [prod_map_inv, op_unop, eqToHom_op, prod_map, Category.comp_id]
    --   ext
    --   dsimp only [op_unop, types_comp_apply, types_id_apply]
    --   simp only [Types.pi_lift_π_apply, op_unop, types_comp_apply]
    --   -- Types.pi_lift_π_apply
    --   sorry



end ExtensiveSheaves

end CategoryTheory
