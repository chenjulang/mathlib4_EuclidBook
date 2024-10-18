/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.Abel

/-!
# Circulant matrices

This file contains the definition and basic results about circulant matrices.
Given a vector `v : n → α` indexed by a type that is endowed with subtraction,
`Matrix.circulant v` is the matrix whose `(i, j)`th entry is `v (i - j)`.

## Main results

- `Matrix.circulant`: the circulant matrix generated by a given vector `v : n → α`.
- `Matrix.circulant_mul`: the product of two circulant matrices `circulant v` and `circulant w` is
                          the circulant matrix generated by `circulant v *ᵥ w`.
- `Matrix.circulant_mul_comm`: multiplication of circulant matrices commutes when the elements do.

## Implementation notes

`Matrix.Fin.foo` is the `Fin n` version of `Matrix.foo`.
Namely, the index type of the circulant matrices in discussion is `Fin n`.

## Tags

circulant, matrix
-/


variable {α β m n R : Type*}

namespace Matrix

open Function

open Matrix

/-- Given the condition `[Sub n]` and a vector `v : n → α`,
    we define `circulant v` to be the circulant matrix generated by `v` of type `Matrix n n α`.
    The `(i,j)`th entry is defined to be `v (i - j)`. -/
def circulant [Sub n] (v : n → α) : Matrix n n α :=
  of fun i j => v (i - j)

-- TODO: set as an equation lemma for `circulant`, see mathlib4#3024
@[simp]
theorem circulant_apply [Sub n] (v : n → α) (i j) : circulant v i j = v (i - j) := rfl

theorem circulant_col_zero_eq [AddGroup n] (v : n → α) (i : n) : circulant v i 0 = v i :=
  congr_arg v (sub_zero _)

theorem circulant_injective [AddGroup n] : Injective (circulant : (n → α) → Matrix n n α) := by
  intro v w h
  ext k
  rw [← circulant_col_zero_eq v, ← circulant_col_zero_eq w, h]

theorem Fin.circulant_injective : ∀ n, Injective fun v : Fin n → α => circulant v
  | 0 => by simp [Injective]
  | _ + 1 => Matrix.circulant_injective

@[simp]
theorem circulant_inj [AddGroup n] {v w : n → α} : circulant v = circulant w ↔ v = w :=
  circulant_injective.eq_iff

@[simp]
theorem Fin.circulant_inj {n} {v w : Fin n → α} : circulant v = circulant w ↔ v = w :=
  (Fin.circulant_injective n).eq_iff

theorem transpose_circulant [AddGroup n] (v : n → α) :
    (circulant v)ᵀ = circulant fun i => v (-i) := by ext; simp

theorem conjTranspose_circulant [Star α] [AddGroup n] (v : n → α) :
    (circulant v)ᴴ = circulant (star fun i => v (-i)) := by ext; simp

theorem Fin.transpose_circulant : ∀ {n} (v : Fin n → α), (circulant v)ᵀ = circulant fun i => v (-i)
  | 0 => by simp [Injective, eq_iff_true_of_subsingleton]
  | _ + 1 => Matrix.transpose_circulant

theorem Fin.conjTranspose_circulant [Star α] :
    ∀ {n} (v : Fin n → α), (circulant v)ᴴ = circulant (star fun i => v (-i))
  | 0 => by simp [Injective, eq_iff_true_of_subsingleton]
  | _ + 1 => Matrix.conjTranspose_circulant

theorem map_circulant [Sub n] (v : n → α) (f : α → β) :
    (circulant v).map f = circulant fun i => f (v i) :=
  ext fun _ _ => rfl

theorem circulant_neg [Neg α] [Sub n] (v : n → α) : circulant (-v) = -circulant v :=
  ext fun _ _ => rfl

@[simp]
theorem circulant_zero (α n) [Zero α] [Sub n] : circulant 0 = (0 : Matrix n n α) :=
  ext fun _ _ => rfl

theorem circulant_add [Add α] [Sub n] (v w : n → α) :
    circulant (v + w) = circulant v + circulant w :=
  ext fun _ _ => rfl

theorem circulant_sub [Sub α] [Sub n] (v w : n → α) :
    circulant (v - w) = circulant v - circulant w :=
  ext fun _ _ => rfl

/-- The product of two circulant matrices `circulant v` and `circulant w` is
    the circulant matrix generated by `circulant v *ᵥ w`. -/
theorem circulant_mul [Semiring α] [Fintype n] [AddGroup n] (v w : n → α) :
    circulant v * circulant w = circulant (circulant v *ᵥ w) := by
  ext i j
  simp only [mul_apply, mulVec, circulant_apply, dotProduct]
  refine Fintype.sum_equiv (Equiv.subRight j) _ _ ?_
  intro x
  simp only [Equiv.subRight_apply, sub_sub_sub_cancel_right]

theorem Fin.circulant_mul [Semiring α] :
    ∀ {n} (v w : Fin n → α), circulant v * circulant w = circulant (circulant v *ᵥ w)
  | 0 => by simp [Injective, eq_iff_true_of_subsingleton]
  | _ + 1 => Matrix.circulant_mul

/-- Multiplication of circulant matrices commutes when the elements do. -/
theorem circulant_mul_comm [CommSemigroup α] [AddCommMonoid α] [Fintype n] [AddCommGroup n]
    (v w : n → α) : circulant v * circulant w = circulant w * circulant v := by
  ext i j
  simp only [mul_apply, circulant_apply, mul_comm]
  refine Fintype.sum_equiv ((Equiv.subLeft i).trans (Equiv.addRight j)) _ _ ?_
  intro x
  simp only [Equiv.trans_apply, Equiv.subLeft_apply, Equiv.coe_addRight, add_sub_cancel_right,
    mul_comm]
  congr 2
  abel

theorem Fin.circulant_mul_comm [CommSemigroup α] [AddCommMonoid α] :
    ∀ {n} (v w : Fin n → α), circulant v * circulant w = circulant w * circulant v
  | 0 => by simp [Injective]
  | _ + 1 => Matrix.circulant_mul_comm

/-- `k • circulant v` is another circulant matrix `circulant (k • v)`. -/
theorem circulant_smul [Sub n] [SMul R α] (k : R) (v : n → α) :
    circulant (k • v) = k • circulant v := rfl

@[simp]
theorem circulant_single_one (α n) [Zero α] [One α] [DecidableEq n] [AddGroup n] :
    circulant (Pi.single 0 1 : n → α) = (1 : Matrix n n α) := by
  ext i j
  simp [one_apply, Pi.single_apply, sub_eq_zero]

@[simp]
theorem circulant_single (n) [Semiring α] [DecidableEq n] [AddGroup n] [Fintype n] (a : α) :
    circulant (Pi.single 0 a : n → α) = scalar n a := by
  ext i j
  simp [Pi.single_apply, diagonal_apply, sub_eq_zero]

/-- Note we use `↑i = 0` instead of `i = 0` as `Fin 0` has no `0`.
This means that we cannot state this with `Pi.single` as we did with `Matrix.circulant_single`. -/
theorem Fin.circulant_ite (α) [Zero α] [One α] :
    ∀ n, circulant (fun i => ite (i.1 = 0) 1 0 : Fin n → α) = 1
  | 0 => by simp [Injective, eq_iff_true_of_subsingleton]
  | n + 1 => by
    rw [← circulant_single_one]
    congr with j
    simp [Pi.single_apply, Fin.ext_iff]

/-- A circulant of `v` is symmetric iff `v` equals its reverse. -/
theorem circulant_isSymm_iff [AddGroup n] {v : n → α} :
    (circulant v).IsSymm ↔ ∀ i, v (-i) = v i := by
  rw [IsSymm, transpose_circulant, circulant_inj, funext_iff]

theorem Fin.circulant_isSymm_iff : ∀ {n} {v : Fin n → α}, (circulant v).IsSymm ↔ ∀ i, v (-i) = v i
  | 0 => by simp [IsSymm.ext_iff, IsEmpty.forall_iff]
  | _ + 1 => Matrix.circulant_isSymm_iff

/-- If `circulant v` is symmetric, `∀ i j : I, v (- i) = v i`. -/
theorem circulant_isSymm_apply [AddGroup n] {v : n → α} (h : (circulant v).IsSymm) (i : n) :
    v (-i) = v i :=
  circulant_isSymm_iff.1 h i

theorem Fin.circulant_isSymm_apply {n} {v : Fin n → α} (h : (circulant v).IsSymm) (i : Fin n) :
    v (-i) = v i :=
  Fin.circulant_isSymm_iff.1 h i

end Matrix
