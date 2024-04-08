/-
Copyright (c) 2024 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.CategoryTheory.Sites.Coverage

/-!

# The functor of points

Given a scheme `X`, the functor of points associated to `X` is the functor
from the category of commutative rings to types sending `R` to
`X(R) = Hom(Spec R, X)`.

This is of course functorial in `X` as well, providing a functor
`Scheme ⥤ CommRingCat ⥤ Type`.

We construct this functor in this file. It turns out that this functor is fully faithful,
which we also prove in this file.

## Definitions:

- Given `X : Scheme`, `X.functorOfPoints` is its associated functor of points.
- `schemeToFunctor` is the functor `Scheme ⥤ CommRingCat ⥤ Type` (with suitable universes).
- `schemeToFunctor` is provided with `Full` and `Faithful` instances.

## Projects

- Notation for `X.functorOfPoints`.
- Characterize the essential image of `schemeToFunctorOfPoints`.

-/

noncomputable section

namespace AlgebraicGeometry

universe v u

open CategoryTheory


/-- The functor of points associated to a scheme. -/
@[simps! obj map]
def Scheme.functorOfPoints (X : Scheme.{u}) : CommRingCat.{u} ⥤ Type u :=
  Spec.rightOp ⋙ yoneda.obj X

/-- A morphism of schemes induces a morphism on the functors of points. -/
@[simps! app]
def Scheme.mapFunctorOfPoints {X Y : Scheme.{u}} (f : X ⟶ Y) :
    X.functorOfPoints ⟶ Y.functorOfPoints :=
  whiskerLeft _ <| yoneda.map f

@[simp]
lemma Scheme.mapFunctorOfPoints_id (X : Scheme.{u}) :
    mapFunctorOfPoints (𝟙 X) = 𝟙 _ :=
  whiskerLeft_id _

@[simp]
lemma Scheme.mapFunctorOfPoints_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    mapFunctorOfPoints (f ≫ g) = mapFunctorOfPoints f ≫ mapFunctorOfPoints g :=
  by simp [mapFunctorOfPoints]

/-- The "functor of points" functor, which sends `X` to `X.functorOfPoints` on objects
and `f` to `Scheme.mapFunctorOfPoints f` on morphisms. -/
@[simps]
def schemeToFunctor : Scheme.{u} ⥤ CommRingCat.{u} ⥤ Type u where
  obj X := X.functorOfPoints
  map f := Scheme.mapFunctorOfPoints f

instance faithfulFunctorOfPoints : Faithful schemeToFunctor where
  map_injective := by
    intro X Y f g h
    let 𝓤 := X.affineOpenCover
    apply 𝓤.openCover.hom_ext
    intro j
    exact congr_arg (fun e => e.app (𝓤.obj j) (𝓤.map j)) h

/-- IMPLEMENTATION DETAIL: This is used to show the fullness of `schemeToFunctor`. -/
def homOfFunctorOfPoints {X Y : Scheme.{u}} (f : X.functorOfPoints ⟶ Y.functorOfPoints) :
    X ⟶ Y :=
  X.affineOpenCover.openCover.glueMorphisms (fun j => f.app _ <| X.affineOpenCover.map _) <| by
    intro i j
    apply schemeToFunctor.map_injective; ext A e : 3
    dsimp at e ⊢
    let 𝓤 := X.affineOpenCover
    obtain ⟨fst',hfst⟩ := Scheme.Spec.map_surjective
      (e ≫ (Limits.pullback.fst : Limits.pullback (𝓤.map i) (𝓤.map j) ⟶ _))
    obtain ⟨snd',hsnd⟩ := Scheme.Spec.map_surjective
      (e ≫ (Limits.pullback.snd : Limits.pullback (𝓤.map i) (𝓤.map j) ⟶ _))
    slice_lhs 1 2 => erw [← hfst]
    slice_rhs 1 2 => erw [← hsnd]
    have hi := congr_fun (f.naturality fst'.unop) (𝓤.map i)
    have hj := congr_fun (f.naturality snd'.unop) (𝓤.map j)
    dsimp at hi hj
    rw [← hi, ← hj]
    simp_rw [hfst, hsnd, Category.assoc, Limits.pullback.condition]

instance fullFunctorOfPoints : Full schemeToFunctor where
  preimage f := homOfFunctorOfPoints f
  witness := by
    intro X Y f
    ext A e : 3
    dsimp [homOfFunctorOfPoints] at e ⊢
    let 𝓤 := X.affineCover
    let 𝓥 := 𝓤.pullbackCover e
    let 𝓦 := 𝓥.affineRefinement
    let ι : 𝓦.openCover ⟶ 𝓥 := Scheme.OpenCover.fromAffineRefinement.{u,u} 𝓥
    apply 𝓦.openCover.hom_ext
    intro j
    dsimp
    have aux : 𝓦.map j ≫ e = ι.app j ≫ Limits.pullback.snd ≫ X.affineCover.map j.fst := by
      have := ι.w j
      dsimp at this
      rw [← this, Category.assoc]
      congr 1
      apply Limits.pullback.condition
    rw [reassoc_of% aux, Scheme.OpenCover.ι_glueMorphisms]
    let ⟨w,hw⟩ := Scheme.Spec.map_surjective (𝓦.map j)
    have := congr_fun (f.naturality w.unop) e
    dsimp at this
    rw [← hw, ← this, hw, aux]
    let ⟨w,hw⟩ := Scheme.Spec.map_surjective (ι.app j ≫ Limits.pullback.snd)
    simp only [← Category.assoc, ← hw]
    exact congr_fun (f.naturality w.unop) (X.affineCover.map j.fst) |>.symm

def IsBasicOpen {A B : CommRingCat.{u}} (ι : A ⟶ B) (f : A) : Prop :=
  letI : Algebra A B := RingHom.toAlgebra ι
  IsLocalization.Away f B

lemma IsBasicOpen.comp_iso {A B B' : CommRingCat.{u}}
    {ι : A ⟶ B} {f : A}
    {ι' : A ⟶ B'}
    (h : IsBasicOpen ι f) (e : B ≅ B') (w : ι ≫ e.hom = ι') :
    IsBasicOpen ι' f := sorry

open TensorProduct in
lemma IsBasicOpen.pushout {A A' B : CommRingCat.{u}} (ι : A ⟶ B) (f : A)
    (h : IsBasicOpen ι f) (g : A ⟶ A') :
    IsBasicOpen (Limits.pushout.inl : A' ⟶ Limits.pushout g ι) (g f) := by
  let _ : Algebra A B := ι.toAlgebra
  let _ : Algebra A A' := g.toAlgebra
  have : IsLocalization.Away f B := h
  let C := A' ⊗[A] B
  have h' : IsLocalization.Away (g f) C := by
    sorry
  let e : .of C ≅ Limits.pushout g ι :=
    (CommRingCat.pushoutCoconeIsColimit _ _).coconePointUniqueUpToIso <|
    Limits.colimit.isColimit _
  let ι' : A' ⟶ .of C := algebraMap A' C
  let h' : IsBasicOpen ι' (g f) := by
    dsimp [IsBasicOpen]
    convert h'
    ext
    symm
    apply Algebra.smul_def
  apply IsBasicOpen.comp_iso h' (e := e)

lemma isOpenImmersion_isBasicOpen
    {A B : CommRingCat.{u}} (ι : A ⟶ B) (f : A) (h : IsBasicOpen ι f) :
    IsOpenImmersion (Scheme.Spec.map ι.op) := by
  let _ : Algebra A B := RingHom.toAlgebra ι
  let _ : IsLocalization.Away f B := h
  let e' : Localization.Away f ≃ₐ[A] B := Localization.algEquiv _ B
  let B' := CommRingCat.of <| Localization.Away f
  let e : B' ≅ B := e'.toRingEquiv.toCommRingCatIso
  let ι' : A ⟶ B' := algebraMap A <| Localization.Away f
  have : ι = ι' ≫ e.hom := by
    ext t
    exact AlgHom.commutes e'.toAlgHom t |>.symm
  rw [this]
  simp only [op_comp, Functor.map_comp]
  suffices IsOpenImmersion (Scheme.Spec.map ι'.op) from inferInstance
  apply Scheme.basic_open_isOpenImmersion

structure indexedZariskiCover (A : CommRingCat.{u}) where
  J : Type v
  B : J → CommRingCat.{u}
  f : J → A
  ι (j : J) : A ⟶ B j
  isBasicOpen (j : J) : IsBasicOpen (ι j) (f j)
  covers : Ideal.span (Set.range f) = ⊤

def indexedZariskiCover.pushout
    {A A' : CommRingCat.{u}} (𝓤 : indexedZariskiCover A) (g : A ⟶ A') :
    indexedZariskiCover A' where
  J := 𝓤.J
  B j := Limits.pushout g (𝓤.ι j)
  f j := g (𝓤.f j)
  ι j := Limits.pushout.inl
  isBasicOpen j := IsBasicOpen.pushout _ _ (𝓤.isBasicOpen _) _
  covers := by
    have aux := 𝓤.covers
    apply_fun Ideal.map g at aux
    have : Ideal.map g ⊤ = ⊤ := by -- TODO: This should me a lemma...
      rw [Ideal.eq_top_iff_one]
      apply Ideal.subset_span
      use 1
      simp
    rw [this] at aux
    have : Ideal.map g (Ideal.span (Set.range 𝓤.f)) = -- TODO: This should be a lemma...
        Ideal.span (Set.range fun j => g (𝓤.f j)) := by
      rw [Ideal.map_span, Set.image_eq_range]
      congr
      ext a
      refine ⟨fun ⟨⟨_,j,rfl⟩,hx⟩ => ⟨j, hx⟩, fun ⟨j,hx⟩ => ⟨⟨_, j, rfl⟩, hx⟩⟩
    rw [this] at aux
    exact aux

lemma indexedZariskiCover.exists_index
    {A : CommRingCat.{u}} (𝓤 : indexedZariskiCover A)
    (p : PrimeSpectrum A) : ∃ j : 𝓤.J, 𝓤.f j ∉ p.asIdeal := by
  by_contra! h
  apply p.IsPrime.ne_top
  suffices ⊤ ≤ p.asIdeal from Submodule.eq_top_iff'.mpr fun x ↦ this trivial
  rw [← 𝓤.covers, Ideal.span_le]
  rintro j ⟨j,rfl⟩
  apply h

def indexedZariskiCover.affineOpenCover {A : CommRingCat.{u}} (𝓤 : indexedZariskiCover A) :
    (Scheme.Spec.obj <| .op A).AffineOpenCover where
  J := 𝓤.J
  obj := 𝓤.B
  map j := Scheme.Spec.map <| 𝓤.ι j |>.op
  f := fun (p : PrimeSpectrum A) => (𝓤.exists_index p).choose
  Covers := fun (p : PrimeSpectrum A) => by
    let j := (𝓤.exists_index p).choose
    let _ : Algebra A (𝓤.B j) := RingHom.toAlgebra <| 𝓤.ι j
    let _ : IsLocalization.Away (𝓤.f j) (𝓤.B j) := 𝓤.isBasicOpen j
    change p ∈ Set.range ⇑(PrimeSpectrum.comap (algebraMap A (𝓤.B j)))
    rw [PrimeSpectrum.localization_away_comap_range (𝓤.B j) (𝓤.f j)]
    exact (𝓤.exists_index p).choose_spec
  IsOpen j := isOpenImmersion_isBasicOpen _ (𝓤.f j) (𝓤.isBasicOpen _)

theorem indexedZariskiCover.desc
    {X : Scheme.{u}}
    {A : CommRingCat.{u}}
    (𝓤 : indexedZariskiCover.{u} A)
    (b : (j : 𝓤.J) → X.functorOfPoints.obj (𝓤.B j))
    (hb : ∀ (i j : 𝓤.J) (C : CommRingCat.{u})
      (ιi : 𝓤.B i ⟶ C) (ιj : 𝓤.B j ⟶ C),
      𝓤.ι i ≫ ιi = 𝓤.ι j ≫ ιj →
      X.functorOfPoints.map ιi (b i) = X.functorOfPoints.map ιj (b j)) :
    X.functorOfPoints.obj A :=
  𝓤.affineOpenCover.openCover.glueMorphisms b <| by
    intro i j
    apply schemeToFunctor.map_injective
    ext A e : 3
    dsimp at e ⊢
    simp only [← Category.assoc]
    obtain ⟨fst,hfst⟩ := Scheme.Spec.map_surjective (e ≫ Limits.pullback.fst)
    obtain ⟨snd,hsnd⟩ := Scheme.Spec.map_surjective (e ≫ Limits.pullback.snd)
    rw [← hfst, ← hsnd]
    apply hb
    apply Quiver.Hom.op_inj
    apply Scheme.Spec.map_injective
    simp only [Opposite.unop_op, op_comp, Functor.map_comp]
    show Scheme.Spec.map fst ≫ _ = Scheme.Spec.map snd ≫ _
    simp_rw [hfst, hsnd, Category.assoc]
    congr 1
    exact Limits.pullback.condition

lemma indexedZariskiCover.restirct_desc
    {X : Scheme.{u}}
    {A : CommRingCat.{u}}
    (𝓤 : indexedZariskiCover.{u} A)
    (b : (j : 𝓤.J) → X.functorOfPoints.obj (𝓤.B j))
    (hb : ∀ (i j : 𝓤.J) (C : CommRingCat.{u})
      (ιi : 𝓤.B i ⟶ C) (ιj : 𝓤.B j ⟶ C),
      𝓤.ι i ≫ ιi = 𝓤.ι j ≫ ιj →
      X.functorOfPoints.map ιi (b i) = X.functorOfPoints.map ιj (b j)) (j : 𝓤.J) :
    X.functorOfPoints.map (𝓤.ι j) (𝓤.desc b hb) = b _ := by
  unfold indexedZariskiCover.desc
  apply Scheme.OpenCover.ι_glueMorphisms

lemma indexedZariskiCover.hom_ext
    {X : Scheme.{u}}
    {A : CommRingCat.{u}}
    (𝓤 : indexedZariskiCover.{u} A)
    (f g : X.functorOfPoints.obj A)
    (h : ∀ j : 𝓤.J, X.functorOfPoints.map (𝓤.ι j) f = X.functorOfPoints.map (𝓤.ι j) g) :
    f = g :=
  𝓤.affineOpenCover.openCover.hom_ext _ _ h

def zariskiCoverage : Coverage (CommRingCat.{u}ᵒᵖ) where
  covering B := { S |
    ∃ (𝓤 : indexedZariskiCover.{u} B.unop),
      S = Presieve.ofArrows (fun j => .op <| 𝓤.B j) (fun j => (𝓤.ι j).op) }
  pullback := by
    rintro ⟨A⟩ ⟨B⟩ ⟨f⟩ S ⟨𝓤,rfl⟩
    dsimp at f 𝓤
    let 𝓥 := 𝓤.pushout f
    let T : Presieve (Opposite.op B) :=
        Presieve.ofArrows (fun j => .op (𝓥.B j)) (fun j => (𝓥.ι j).op)
    refine ⟨T, ⟨𝓥,rfl⟩, ?_⟩
    rintro _ _ ⟨j⟩
    refine ⟨.op (𝓤.B j), Limits.pushout.inr.op, (𝓤.ι j).op, .mk j, ?_⟩
    rw [← op_comp, ← Limits.pushout.condition]
    rfl

def zariskiTopology : GrothendieckTopology (CommRingCat.{u}ᵒᵖ) :=
  zariskiCoverage.toGrothendieck

lemma Scheme.isSheaf (X : Scheme.{u}) :
    Presheaf.IsSheaf zariskiTopology (unopUnop _ ⋙ X.functorOfPoints) := by
  dsimp [zariskiTopology]
  rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_coverage]
  rintro B S ⟨𝓤,rfl⟩ x hx
  let b : (j : 𝓤.J) → X.functorOfPoints.obj (𝓤.B j) := fun j => x (𝓤.ι j).op <| .mk _
  have hb : ∀ (i j : 𝓤.J) (C : CommRingCat.{u})
      (ιi : 𝓤.B i ⟶ C) (ιj : 𝓤.B j ⟶ C),
      𝓤.ι i ≫ ιi = 𝓤.ι j ≫ ιj →
      X.functorOfPoints.map ιi (b i) = X.functorOfPoints.map ιj (b j) := by
    intro i j C ιi ιj h
    apply hx
    apply_fun (fun q => q.op) at h
    exact h
  let t := 𝓤.desc b hb
  refine ⟨t,?_,?_⟩
  · rintro X f ⟨j⟩
    apply indexedZariskiCover.restirct_desc
  · intro e he
    apply indexedZariskiCover.hom_ext
    intro j
    have := he (𝓤.ι j).op (.mk j)
    dsimp at this ⊢
    rw [this]
    have := 𝓤.restirct_desc b hb j
    dsimp [t] at this ⊢
    rw [this]

@[simps]
def schemeToSheaf : Scheme ⥤ Sheaf zariskiTopology.{u} (Type u) where
  obj X := ⟨unopUnop _ ⋙ X.functorOfPoints, X.isSheaf⟩
  map f := .mk <| whiskerLeft _ <| Scheme.mapFunctorOfPoints f
  --map_id := _
  --map_comp := _

instance : Faithful schemeToSheaf where
  map_injective := by
    intro X Y f g h
    apply schemeToFunctor.map_injective
    apply_fun (fun e => whiskerLeft (opOp _) e.val) at h
    exact h

instance : Full schemeToSheaf where
  preimage f := Full.preimage (F := schemeToFunctor) (whiskerLeft (opOp _) f.val)
  witness f := by
    apply Sheaf.Hom.ext
    have := Full.witness (F := schemeToFunctor) (whiskerLeft (opOp _) f.val)
    dsimp at this ⊢
    rw [this]
    rfl

end AlgebraicGeometry
