/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, David Kurniadi Angdinata
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Weierstrass equations of elliptic curves

This file defines the structure of an elliptic curve as a nonsingular Weierstrass curve given by a
Weierstrass equation, which is mathematically accurate in many cases but also good for computation.

## Mathematical background

Let `S` be a scheme. The actual category of elliptic curves over `S` is a large category, whose
objects are schemes `E` equipped with a map `E → S`, a section `S → E`, and some axioms (the map
is smooth and proper and the fibres are geometrically-connected one-dimensional group varieties). In
the special case where `S` is the spectrum of some commutative ring `R` whose Picard group is zero
(this includes all fields, all PIDs, and many other commutative rings) it can be shown (using a lot
of algebro-geometric machinery) that every elliptic curve `E` is a projective plane cubic isomorphic
to a Weierstrass curve given by the equation $Y^2 + a_1XY + a_3Y = X^3 + a_2X^2 + a_4X + a_6$ for
some $a_i$ in `R`, and such that a certain quantity called the discriminant of `E` is a unit in `R`.
If `R` is a field, this quantity divides the discriminant of a cubic polynomial whose roots over a
splitting field of `R` are precisely the $X$-coordinates of the non-zero 2-torsion points of `E`.

## Main definitions

 * `WeierstrassCurve`: a Weierstrass curve over a commutative ring.
 * `WeierstrassCurve.Δ`: the discriminant of a Weierstrass curve.
 * `WeierstrassCurve.map`: the Weierstrass curve mapped over a ring homomorphism.
 * `WeierstrassCurve.twoTorsionPolynomial`: the 2-torsion polynomial of a Weierstrass curve.
 * `WeierstrassCurve.Elliptic`: typeclass asserts that a Weierstrass curve is an elliptic curve.
 * `WeierstrassCurve.j`: the j-invariant of an elliptic curve.
 * `WeierstrassCurve.ofJ0`: an elliptic curve whose j-invariant is 0.
 * `WeierstrassCurve.ofJ1728`: an elliptic curve whose j-invariant is 1728.
 * `WeierstrassCurve.ofJNe0Or1728`: an elliptic curve whose j-invariant is neither 0 nor 1728.
 * `WeierstrassCurve.ofJ`: an elliptic curve whose j-invariant equal to j.

## Main statements

 * `WeierstrassCurve.twoTorsionPolynomial_disc`: the discriminant of a Weierstrass curve is a
    constant factor of the cubic discriminant of its 2-torsion polynomial.
 * `WeierstrassCurve.ofJ_j`: the j-invariant of `WeierstrassCurve.ofJ` is equal to j.

## Implementation notes

The definition of elliptic curves in this file makes sense for all commutative rings `R`, but it
only gives a type which can be beefed up to a category which is equivalent to the category of
elliptic curves over the spectrum $\mathrm{Spec}(R)$ of `R` in the case that `R` has trivial Picard
group $\mathrm{Pic}(R)$ or, slightly more generally, when its 12-torsion is trivial. The issue is
that for a general ring `R`, there might be elliptic curves over $\mathrm{Spec}(R)$ in the sense of
algebraic geometry which are not globally defined by a cubic equation valid over the entire base.

## References

 * [N Katz and B Mazur, *Arithmetic Moduli of Elliptic Curves*][katz_mazur]
 * [P Deligne, *Courbes Elliptiques: Formulaire (d'après J. Tate)*][deligne_formulaire]
 * [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, j invariant
-/

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow])

universe s u v w

/-! ## Weierstrass curves -/

/-- A Weierstrass curve $Y^2 + a_1XY + a_3Y = X^3 + a_2X^2 + a_4X + a_6$ with parameters $a_i$. -/
@[ext]
structure WeierstrassCurve (R : Type u) where
  /-- The `a₁` coefficient of a Weierstrass curve. -/
  a₁ : R
  /-- The `a₂` coefficient of a Weierstrass curve. -/
  a₂ : R
  /-- The `a₃` coefficient of a Weierstrass curve. -/
  a₃ : R
  /-- The `a₄` coefficient of a Weierstrass curve. -/
  a₄ : R
  /-- The `a₆` coefficient of a Weierstrass curve. -/
  a₆ : R

namespace WeierstrassCurve


instance instInhabited {R : Type u} [Inhabited R] :
    Inhabited <| WeierstrassCurve R :=
  ⟨⟨default, default, default, default, default⟩⟩

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

section Quantity

/-! ### Standard quantities -/

/-- The `b₂` coefficient of a Weierstrass curve. -/
def b₂ : R :=
  W.a₁ ^ 2 + 4 * W.a₂

/-- The `b₄` coefficient of a Weierstrass curve. -/
def b₄ : R :=
  2 * W.a₄ + W.a₁ * W.a₃

/-- The `b₆` coefficient of a Weierstrass curve. -/
def b₆ : R :=
  W.a₃ ^ 2 + 4 * W.a₆

/-- The `b₈` coefficient of a Weierstrass curve. -/
def b₈ : R :=
  W.a₁ ^ 2 * W.a₆ + 4 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2

lemma b_relation : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := by
  simp only [b₂, b₄, b₆, b₈]
  ring1

/-- The `c₄` coefficient of a Weierstrass curve. -/
def c₄ : R :=
  W.b₂ ^ 2 - 24 * W.b₄

/-- The `c₆` coefficient of a Weierstrass curve. -/
def c₆ : R :=
  -W.b₂ ^ 3 + 36 * W.b₂ * W.b₄ - 216 * W.b₆

/-- The discriminant `Δ` of a Weierstrass curve. If `R` is a field, then this polynomial vanishes
if and only if the cubic curve cut out by this equation is singular. Sometimes only defined up to
sign in the literature; we choose the sign used by the LMFDB. For more discussion, see
[the LMFDB page on discriminants](https://www.lmfdb.org/knowledge/show/ec.discriminant). -/
def Δ : R :=
  -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2 + 9 * W.b₂ * W.b₄ * W.b₆

lemma c_relation : 1728 * W.Δ = W.c₄ ^ 3 - W.c₆ ^ 2 := by
  simp only [b₂, b₄, b₆, b₈, c₄, c₆, Δ]
  ring1

section CharTwo

variable [CharP R 2]

lemma b₂_of_char_two : W.b₂ = W.a₁ ^ 2 := by
  rw [b₂]
  linear_combination 2 * W.a₂ * CharP.cast_eq_zero R 2

lemma b₄_of_char_two : W.b₄ = W.a₁ * W.a₃ := by
  rw [b₄]
  linear_combination W.a₄ * CharP.cast_eq_zero R 2

lemma b₆_of_char_two : W.b₆ = W.a₃ ^ 2 := by
  rw [b₆]
  linear_combination 2 * W.a₆ * CharP.cast_eq_zero R 2

lemma b₈_of_char_two :
    W.b₈ = W.a₁ ^ 2 * W.a₆ + W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 + W.a₄ ^ 2 := by
  rw [b₈]
  linear_combination (2 * W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ - W.a₄ ^ 2) * CharP.cast_eq_zero R 2

lemma c₄_of_char_two : W.c₄ = W.a₁ ^ 4 := by
  rw [c₄, b₂_of_char_two]
  linear_combination -12 * W.b₄ * CharP.cast_eq_zero R 2

lemma c₆_of_char_two : W.c₆ = W.a₁ ^ 6 := by
  rw [c₆, b₂_of_char_two]
  linear_combination (18 * W.a₁ ^ 2 * W.b₄ - 108 * W.b₆ - W.a₁ ^ 6) * CharP.cast_eq_zero R 2

lemma Δ_of_char_two : W.Δ = W.a₁ ^ 4 * W.b₈ + W.a₃ ^ 4 + W.a₁ ^ 3 * W.a₃ ^ 3 := by
  rw [Δ, b₂_of_char_two, b₄_of_char_two, b₆_of_char_two]
  linear_combination (-W.a₁ ^ 4 * W.b₈ - 14 * W.a₃ ^ 4) * CharP.cast_eq_zero R 2

lemma b_relation_of_char_two : W.b₂ * W.b₆ = W.b₄ ^ 2 := by
  linear_combination -W.b_relation + 2 * W.b₈ * CharP.cast_eq_zero R 2

lemma c_relation_of_char_two : W.c₄ ^ 3 = W.c₆ ^ 2 := by
  linear_combination -W.c_relation + 864 * W.Δ * CharP.cast_eq_zero R 2

end CharTwo

section CharThree

variable [CharP R 3]

lemma b₂_of_char_three : W.b₂ = W.a₁ ^ 2 + W.a₂ := by
  rw [b₂]
  linear_combination W.a₂ * CharP.cast_eq_zero R 3

lemma b₄_of_char_three : W.b₄ = -W.a₄ + W.a₁ * W.a₃ := by
  rw [b₄]
  linear_combination W.a₄ * CharP.cast_eq_zero R 3

lemma b₆_of_char_three : W.b₆ = W.a₃ ^ 2 + W.a₆ := by
  rw [b₆]
  linear_combination W.a₆ * CharP.cast_eq_zero R 3

lemma b₈_of_char_three :
    W.b₈ = W.a₁ ^ 2 * W.a₆ + W.a₂ * W.a₆ - W.a₁ * W.a₃ * W.a₄ + W.a₂ * W.a₃ ^ 2 - W.a₄ ^ 2 := by
  rw [b₈]
  linear_combination W.a₂ * W.a₆ * CharP.cast_eq_zero R 3

lemma c₄_of_char_three : W.c₄ = W.b₂ ^ 2 := by
  rw [c₄]
  linear_combination -8 * W.b₄ * CharP.cast_eq_zero R 3

lemma c₆_of_char_three : W.c₆ = -W.b₂ ^ 3 := by
  rw [c₆]
  linear_combination (12 * W.b₂ * W.b₄ - 72 * W.b₆) * CharP.cast_eq_zero R 3

lemma Δ_of_char_three : W.Δ = -W.b₂ ^ 2 * W.b₈ - 8 * W.b₄ ^ 3 := by
  rw [Δ]
  linear_combination (-9 * W.b₆ ^ 2 + 3 * W.b₂ * W.b₄ * W.b₆) * CharP.cast_eq_zero R 3

lemma b_relation_of_char_three : W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2 := by
  linear_combination W.b_relation - W.b₈ * CharP.cast_eq_zero R 3

lemma c_relation_of_char_three : W.c₄ ^ 3 = W.c₆ ^ 2 := by
  linear_combination -W.c_relation + 576 * W.Δ * CharP.cast_eq_zero R 3

end CharThree

end Quantity

section BaseChange

/-! ### Maps and base changes -/

variable {A : Type v} [CommRing A] (φ : R →+* A)

/-- The Weierstrass curve mapped over a ring homomorphism `φ : R →+* A`. -/
@[simps]
def map : WeierstrassCurve A :=
  ⟨φ W.a₁, φ W.a₂, φ W.a₃, φ W.a₄, φ W.a₆⟩

variable (A)

/-- The Weierstrass curve base changed to an algebra `A` over `R`. -/
abbrev baseChange [Algebra R A] : WeierstrassCurve A :=
  W.map <| algebraMap R A

variable {A}

@[simp]
lemma map_b₂ : (W.map φ).b₂ = φ W.b₂ := by
  simp only [b₂, map_a₁, map_a₂]
  map_simp

@[simp]
lemma map_b₄ : (W.map φ).b₄ = φ W.b₄ := by
  simp only [b₄, map_a₁, map_a₃, map_a₄]
  map_simp

@[simp]
lemma map_b₆ : (W.map φ).b₆ = φ W.b₆ := by
  simp only [b₆, map_a₃, map_a₆]
  map_simp

@[simp]
lemma map_b₈ : (W.map φ).b₈ = φ W.b₈ := by
  simp only [b₈, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  map_simp

@[simp]
lemma map_c₄ : (W.map φ).c₄ = φ W.c₄ := by
  simp only [c₄, map_b₂, map_b₄]
  map_simp

@[simp]
lemma map_c₆ : (W.map φ).c₆ = φ W.c₆ := by
  simp only [c₆, map_b₂, map_b₄, map_b₆]
  map_simp

@[simp]
lemma map_Δ : (W.map φ).Δ = φ W.Δ := by
  simp only [Δ, map_b₂, map_b₄, map_b₆, map_b₈]
  map_simp

@[simp]
lemma map_id : W.map (RingHom.id R) = W :=
  rfl

lemma map_map {B : Type w} [CommRing B] (ψ : A →+* B) : (W.map φ).map ψ = W.map (ψ.comp φ) :=
  rfl

@[simp]
lemma map_baseChange {S : Type s} [CommRing S] [Algebra R S] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra S A] [IsScalarTower R S A] {B : Type w} [CommRing B] [Algebra R B] [Algebra S B]
    [IsScalarTower R S B] (ψ : A →ₐ[S] B) : (W.baseChange A).map ψ = W.baseChange B :=
  congr_arg W.map <| ψ.comp_algebraMap_of_tower R

lemma map_injective {φ : R →+* A} (hφ : Function.Injective φ) :
    Function.Injective <| map (φ := φ) := fun _ _ h => by
  rcases mk.inj h with ⟨_, _, _, _, _⟩
  ext <;> apply_fun _ using hφ <;> assumption

end BaseChange

section TorsionPolynomial

/-! ### 2-torsion polynomials -/

/-- A cubic polynomial whose discriminant is a multiple of the Weierstrass curve discriminant. If
`W` is an elliptic curve over a field `R` of characteristic different from 2, then its roots over a
splitting field of `R` are precisely the $X$-coordinates of the non-zero 2-torsion points of `W`. -/
def twoTorsionPolynomial : Cubic R :=
  ⟨4, W.b₂, 2 * W.b₄, W.b₆⟩

lemma twoTorsionPolynomial_disc : W.twoTorsionPolynomial.disc = 16 * W.Δ := by
  simp only [b₂, b₄, b₆, b₈, Δ, twoTorsionPolynomial, Cubic.disc]
  ring1

section CharTwo

variable [CharP R 2]

lemma twoTorsionPolynomial_of_char_two : W.twoTorsionPolynomial = ⟨0, W.b₂, 0, W.b₆⟩ := by
  rw [twoTorsionPolynomial]
  ext <;> dsimp
  · linear_combination 2 * CharP.cast_eq_zero R 2
  · linear_combination W.b₄ * CharP.cast_eq_zero R 2

lemma twoTorsionPolynomial_disc_of_char_two : W.twoTorsionPolynomial.disc = 0 := by
  linear_combination W.twoTorsionPolynomial_disc + 8 * W.Δ * CharP.cast_eq_zero R 2

end CharTwo

section CharThree

variable [CharP R 3]

lemma twoTorsionPolynomial_of_char_three : W.twoTorsionPolynomial = ⟨1, W.b₂, -W.b₄, W.b₆⟩ := by
  rw [twoTorsionPolynomial]
  ext <;> dsimp
  · linear_combination CharP.cast_eq_zero R 3
  · linear_combination W.b₄ * CharP.cast_eq_zero R 3

lemma twoTorsionPolynomial_disc_of_char_three : W.twoTorsionPolynomial.disc = W.Δ := by
  linear_combination W.twoTorsionPolynomial_disc + 5 * W.Δ * CharP.cast_eq_zero R 3

end CharThree

lemma twoTorsionPolynomial_disc_isUnit [Invertible (2 : R)] :
    IsUnit W.twoTorsionPolynomial.disc ↔ IsUnit W.Δ := by
  rw [twoTorsionPolynomial_disc, IsUnit.mul_iff, show (16 : R) = 2 ^ 4 by norm_num1]
  exact and_iff_right <| isUnit_of_invertible <| 2 ^ 4

lemma twoTorsionPolynomial_disc_ne_zero [Nontrivial R] [Invertible (2 : R)] (hΔ : IsUnit W.Δ) :
    W.twoTorsionPolynomial.disc ≠ 0 :=
  (W.twoTorsionPolynomial_disc_isUnit.mpr hΔ).ne_zero

end TorsionPolynomial

section ModelsWithJ

/-! ### Models with prescribed j-invariant -/

variable (R)

/-- The Weierstrass curve $Y^2 + Y = X^3$. It is of j-invariant 0 if it is an elliptic curve. -/
def ofJ0 : WeierstrassCurve R :=
  ⟨0, 0, 1, 0, 0⟩

lemma ofJ0_c₄ : (ofJ0 R).c₄ = 0 := by
  rw [ofJ0, c₄, b₂, b₄]
  norm_num1

lemma ofJ0_Δ : (ofJ0 R).Δ = -27 := by
  rw [ofJ0, Δ, b₂, b₄, b₆, b₈]
  norm_num1

/-- The Weierstrass curve $Y^2 = X^3 + X$. It is of j-invariant 1728 if it is an elliptic curve. -/
def ofJ1728 : WeierstrassCurve R :=
  ⟨0, 0, 0, 1, 0⟩

lemma ofJ1728_c₄ : (ofJ1728 R).c₄ = -48 := by
  rw [ofJ1728, c₄, b₂, b₄]
  norm_num1

lemma ofJ1728_Δ : (ofJ1728 R).Δ = -64 := by
  rw [ofJ1728, Δ, b₂, b₄, b₆, b₈]
  norm_num1

variable {R} (j : R)

/-- The Weierstrass curve $Y^2 + (j - 1728)XY = X^3 - 36(j - 1728)^3X - (j - 1728)^5$.
It is of j-invariant j if it is an elliptic curve. -/
def ofJNe0Or1728 : WeierstrassCurve R :=
  ⟨j - 1728, 0, 0, -36 * (j - 1728) ^ 3, -(j - 1728) ^ 5⟩

lemma ofJNe0Or1728_c₄ : (ofJNe0Or1728 j).c₄ = j * (j - 1728) ^ 3 := by
  simp only [ofJNe0Or1728, c₄, b₂, b₄]
  ring1

lemma ofJNe0Or1728_Δ : (ofJNe0Or1728 j).Δ = j ^ 2 * (j - 1728) ^ 9 := by
  simp only [ofJNe0Or1728, Δ, b₂, b₄, b₆, b₈]
  ring1

end ModelsWithJ

/-! ## Elliptic curves -/

/-- `WeierstrassCurve.Elliptic` is a typeclass which asserts that a Weierstrass curve is an
elliptic curve, that is, its discriminant is invertible.
It is a `Type` rather than `Prop` since it contains
a (unique) choice of the inverse of the discriminant.
Note that this definition is only mathematically
accurate for certain rings whose Picard group has trivial 12-torsion, such as a field or a PID. -/
protected abbrev Elliptic := Invertible W.Δ

variable [W.Elliptic]

variable {W} in
abbrev Elliptic.copy (W' : WeierstrassCurve R) (h : W' = W) : W'.Elliptic :=
  Invertible.copy ‹Invertible W.Δ› W'.Δ (by rw [h])

/-- The discriminant `Δ'` of an elliptic curve over `R`, which is given as a unit in `R`. -/
def Δ' : Rˣ := unitOfInvertible W.Δ

@[congr]
lemma Δ'_eq_of_eq (W' : WeierstrassCurve R) [W'.Elliptic] (h : W = W') : W.Δ' = W'.Δ' := by
  subst h
  congr
  apply Subsingleton.allEq

/-- The discriminant `Δ'` of an elliptic curve is equal to the
discriminant `Δ` of it as a Weierstrass curve. -/
lemma coe_Δ' : W.Δ' = W.Δ := rfl

/-- The j-invariant `j` of an elliptic curve, which is invariant under isomorphisms over `R`. -/
def j : R :=
  W.Δ'⁻¹ * W.c₄ ^ 3

@[congr]
lemma j_eq_of_eq (W' : WeierstrassCurve R) [W'.Elliptic] (h : W = W') : W.j = W'.j := by
  simp_rw [j, Δ'_eq_of_eq _ _ h, h]

/-- A variant of `WeierstrassCurve.j_eq_zero_iff` without assuming a reduced ring. -/
lemma j_eq_zero_iff' : W.j = 0 ↔ W.c₄ ^ 3 = 0 := by
  rw [j, Units.mul_right_eq_zero]

lemma j_eq_zero (h : W.c₄ = 0) : W.j = 0 := by
  rw [j_eq_zero_iff', h, zero_pow three_ne_zero]

lemma j_eq_zero_iff [IsReduced R] : W.j = 0 ↔ W.c₄ = 0 := by
  rw [j_eq_zero_iff', IsReduced.pow_eq_zero_iff three_ne_zero]

section CharTwo

variable [CharP R 2]

lemma j_of_char_two : W.j = W.Δ'⁻¹ * W.a₁ ^ 12 := by
  rw [j, W.c₄_of_char_two, ← pow_mul]

/-- A variant of `WeierstrassCurve.j_eq_zero_iff_of_char_two` without assuming a reduced ring. -/
lemma j_eq_zero_iff_of_char_two' : W.j = 0 ↔ W.a₁ ^ 12 = 0 := by
  rw [j_of_char_two, Units.mul_right_eq_zero]

lemma j_eq_zero_of_char_two (h : W.a₁ = 0) : W.j = 0 := by
  rw [j_eq_zero_iff_of_char_two', h, zero_pow (Nat.succ_ne_zero _)]

lemma j_eq_zero_iff_of_char_two [IsReduced R] : W.j = 0 ↔ W.a₁ = 0 := by
  rw [j_eq_zero_iff_of_char_two', IsReduced.pow_eq_zero_iff (Nat.succ_ne_zero _)]

end CharTwo

section CharThree

variable [CharP R 3]

lemma j_of_char_three : W.j = W.Δ'⁻¹ * W.b₂ ^ 6 := by
  rw [j, W.c₄_of_char_three, ← pow_mul]

/-- A variant of `WeierstrassCurve.j_eq_zero_iff_of_char_three` without assuming a reduced ring. -/
lemma j_eq_zero_iff_of_char_three' : W.j = 0 ↔ W.b₂ ^ 6 = 0 := by
  rw [j_of_char_three, Units.mul_right_eq_zero]

lemma j_eq_zero_of_char_three (h : W.b₂ = 0) : W.j = 0 := by
  rw [j_eq_zero_iff_of_char_three', h, zero_pow (Nat.succ_ne_zero _)]

lemma j_eq_zero_iff_of_char_three [IsReduced R] : W.j = 0 ↔ W.b₂ = 0 := by
  rw [j_eq_zero_iff_of_char_three', IsReduced.pow_eq_zero_iff (Nat.succ_ne_zero _)]

end CharThree

lemma twoTorsionPolynomial_disc_ne_zero_of_elliptic [Nontrivial R] [Invertible (2 : R)] :
    W.twoTorsionPolynomial.disc ≠ 0 :=
  W.twoTorsionPolynomial_disc_ne_zero (isUnit_of_invertible _)

section BaseChange

/-! ### Maps and base changes -/

variable {A : Type v} [CommRing A] (φ : R →+* A)

instance Elliptic.map : (W.map φ).Elliptic := (Invertible.map φ W.Δ).copy _ (W.map_Δ _)

set_option linter.docPrime false in
lemma coe_map_Δ' : (W.map φ).Δ' = φ W.Δ' := by
  simp_rw [coe_Δ', map_Δ]

set_option linter.docPrime false in
@[simp]
lemma map_Δ' : (W.map φ).Δ' = (Units.map ↑φ) W.Δ' := by
  ext; exact W.coe_map_Δ' φ

set_option linter.docPrime false in
lemma coe_inv_map_Δ' : (W.map φ).Δ'⁻¹ = φ ↑W.Δ'⁻¹ :=
  rfl

@[simp]
lemma map_j : (W.map φ).j = φ W.j := by
  simp_rw [j, map_c₄, coe_inv_map_Δ', map_mul, map_pow]

end BaseChange

section ModelsWithJ

/-! ### Models with prescribed j-invariant -/

variable (R)

/-- When 3 is invertible, $Y^2 + Y = X^3$ is an elliptic curve.
It is of j-invariant 0 (see `WeierstrassCurve.ofJ0_j`). -/
instance Elliptic.ofJ0 [Invertible (3 : R)] : (ofJ0 R).Elliptic :=
  (invertibleNeg (3 ^ 3 : R)).copy _ (by rw [ofJ0_Δ R]; norm_num1)

lemma ofJ0_j [Invertible (3 : R)] : (ofJ0 R).j = 0 := by
  simp only [j, ofJ0_c₄]
  ring1

/-- When 2 is invertible, $Y^2 = X^3 + X$ is an elliptic curve.
It is of j-invariant 1728 (see `WeierstrassCurve.ofJ1728_j`). -/
instance Elliptic.ofJ1728 [Invertible (2 : R)] : (ofJ1728 R).Elliptic :=
  (invertibleNeg (2 ^ 6 : R)).copy _ (by rw [ofJ1728_Δ R]; norm_num1)

lemma ofJ1728_j [Invertible (2 : R)] : (ofJ1728 R).j = 1728 := by
  field_simp [j, ofJ1728_c₄, coe_Δ', ofJ1728_Δ]
  norm_num1

variable {R}

/-- When j and j - 1728 are both invertible,
$Y^2 + (j - 1728)XY = X^3 - 36(j - 1728)^3X - (j - 1728)^5$ is an elliptic curve.
It is of j-invariant j (see `WeierstrassCurve.ofJNe0Or1728_j`). -/
instance Elliptic.ofJNe0Or1728 (j : R) [Invertible j] [Invertible (j - 1728)] :
    (ofJNe0Or1728 j).Elliptic :=
  (invertibleMul (j ^ 2) ((j - 1728) ^ 9)).copy _ (ofJNe0Or1728_Δ j)

lemma ofJNe0Or1728_j (j : R) [Invertible j] [Invertible (j - 1728)] :
    (ofJNe0Or1728 j).j = j := by
  field_simp [WeierstrassCurve.j, ofJNe0Or1728_c₄, coe_Δ', ofJNe0Or1728_Δ]
  ring1

variable {F : Type u} [Field F] (j : F)

variable [DecidableEq F]

/-- For any element j of a field $F$, there exists an elliptic curve over $F$
with j-invariant equal to j (see `WeierstrassCurve.ofJ_j`).
Its coefficients are given explicitly (see `WeierstrassCurve.ofJ0`, `WeierstrassCurve.ofJ1728`
and `WeierstrassCurve.ofJNe0Or1728`). -/
def ofJ : WeierstrassCurve F :=
  if j = 0 then
    if (3 : F) = 0 then
      ofJ1728 F
    else
      ofJ0 F
  else if j = 1728 then
    ofJ1728 F
  else
    ofJNe0Or1728 j

lemma ofJ_0_of_three_ne_zero [h3 : NeZero (3 : F)] :
    ofJ 0 = ofJ0 F := by
  rw [ofJ, if_pos rfl, if_neg h3.out]

lemma ofJ_0_of_three_eq_zero (h3 : (3 : F) = 0) :
    ofJ 0 = ofJ1728 F := by
  rw [ofJ, if_pos rfl, if_pos h3]

lemma ofJ_0_of_two_eq_zero (h2 : (2 : F) = 0) :
    ofJ 0 = ofJ0 F := by
  rw [ofJ, if_pos rfl, if_neg ((show (3 : F) = 1 by linear_combination h2) ▸ one_ne_zero)]

lemma ofJ_1728_of_three_eq_zero (h3 : (3 : F) = 0) :
    ofJ 1728 = ofJ1728 F := by
  rw [ofJ, if_pos (show (1728 : F) = 0 by linear_combination 576 * h3), if_pos h3]

lemma ofJ_1728_of_two_ne_zero [h2 : NeZero (2 : F)] :
    ofJ 1728 = ofJ1728 F := by
  by_cases h3 : (3 : F) = 0
  · rw [ofJ, if_pos (show (1728 : F) = 0 by linear_combination 576 * h3), if_pos h3]
  · have h : (1728 : F) ≠ 0 := fun h => or_iff_not_and_not.mp
      (mul_eq_zero.mp <| by rwa [show 2 ^ 6 * 3 ^ 3 = (1728 : F) by norm_num1])
      ⟨pow_ne_zero 6 h2.out, pow_ne_zero 3 h3⟩
    rw [ofJ, if_neg h, if_pos rfl]

lemma ofJ_1728_of_two_eq_zero (h2 : (2 : F) = 0) :
    ofJ 1728 = ofJ0 F := by
  rw [ofJ, if_pos (show (1728 : F) = 0 by linear_combination 864 * h2),
    if_neg ((show (3 : F) = 1 by linear_combination h2) ▸ one_ne_zero)]

lemma ofJ_ne_0_ne_1728 (h0 : j ≠ 0) (h1728 : j ≠ 1728) : ofJ j =
    ofJNe0Or1728 j := by
  rw [ofJ, if_neg h0, if_neg h1728]

instance Elliptic.ofJ : (ofJ j).Elliptic :=
  if h0 : j = 0 then
    if h3 : (3 : F) = 0 then
      have h : (2 : F) * 2 = 1 := by linear_combination h3
      letI : Invertible (2 : F) := ⟨2, h, h⟩
      Elliptic.copy _ (h0 ▸ ofJ_0_of_three_eq_zero h3)
    else
      haveI := NeZero.mk h3
      letI := invertibleOfNonzero h3
      Elliptic.copy _ (h0 ▸ ofJ_0_of_three_ne_zero)
  else if h1728 : j = 1728 then
    have h2 : (2 : F) ≠ 0 := fun h ↦ h0 (by linear_combination h1728 + 864 * h)
    haveI := NeZero.mk h2
    letI := invertibleOfNonzero h2
    Elliptic.copy _ (h1728 ▸ ofJ_1728_of_two_ne_zero)
  else
    letI := invertibleOfNonzero h0
    letI := invertibleOfNonzero (sub_ne_zero.2 h1728)
    Elliptic.copy _ (ofJ_ne_0_ne_1728 j h0 h1728)

lemma ofJ_j : (ofJ j).j = j := by
  by_cases h0 : j = 0
  · by_cases h3 : (3 : F) = 0
    · have h : (2 : F) * 2 = 1 := by linear_combination h3
      letI : Invertible (2 : F) := ⟨2, h, h⟩
      rw [j_eq_of_eq _ _ (h0 ▸ ofJ_0_of_three_eq_zero h3), ofJ1728_j, h0]
      linear_combination 576 * h3
    · haveI := NeZero.mk h3
      letI := invertibleOfNonzero h3
      rw [j_eq_of_eq _ _ (h0 ▸ ofJ_0_of_three_ne_zero), ofJ0_j, h0]
  · by_cases h1728 : j = 1728
    · have h2 : (2 : F) ≠ 0 := fun h ↦ h0 (by linear_combination h1728 + 864 * h)
      haveI := NeZero.mk h2
      letI := invertibleOfNonzero h2
      rw [j_eq_of_eq _ _ (h1728 ▸ ofJ_1728_of_two_ne_zero), ofJ1728_j, h1728]
    · letI := invertibleOfNonzero h0
      letI := invertibleOfNonzero (sub_ne_zero.2 h1728)
      rw [j_eq_of_eq _ _ (ofJ_ne_0_ne_1728 j h0 h1728), ofJNe0Or1728_j]

instance instInhabitedElliptic : Inhabited ((W : WeierstrassCurve F) × W.Elliptic) :=
  ⟨⟨ofJ 37, inferInstance⟩⟩

end ModelsWithJ

end WeierstrassCurve
