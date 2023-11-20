/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.PowAssoc
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.PNat.Defs
import Mathlib.Data.PNat.Basic
import Mathlib.Util.AssertExists
import Mathlib.Data.Polynomial.Degree.Definitions
import Mathlib.Data.Polynomial.Induction

/-!
# Scalar-multiple polynomial evaluation over commutative semirings

This file defines polynomial evaluation via scalar multiplication.  Our polynomials have
coefficients in a commutative semiring `R`, and we evaluate at a weak form of `R`-algebra, namely a
commutative monoid with a multiplicative action of `R` and a notion of power.  We will later prove
stronger results for power-associative `R`-algebras.  This is analogous to `Data.Polynomial.Eval`,
the difference being that the former is about `*`, while the present file is about `•`.

## Main definitions

* `Polynomial.smnueval`: function for evaluating a polynomial with coefficients in a `CommSemiring`
`R` and vanishing constant term at an element in a non-unital power-associative `R`-algebra.

* `Polynomial.smeval`: function for evaluating a polynomial with coefficients in a `CommSemiring`
`R` at an element in a power-associative `R`-algebra.

## Things I need

* I was hoping for `NonUnitalPowAssocMul` and `PowAssocMul` in Mathlib.Algebra.Group.Defs.  However,
the consensus is that we can just use `Prop`-valued mixin and write a `Pow` instance.

* Maybe put `NonUnitalPowAssocSemiring` and `PowAssocSemiring` in Mathlib.Algebra.Ring.Defs.
Once again, I guess we just use the mixin: `[NonUnitalPowAssocSemiring A] [Powassoc A]`

* I should make a ncpoly class, for polynomials with no constant.  Notation should be `XR[X]`.  For
now we use `Finsupp` ℕ+ →₀ R, so `p.support` is a `Finset ℕ+`, `p.sum` is a sum over that.  Maybe
write a function that restricts a polynomial to a ncpoly, and one that extends a ncpoly to poly.

-- A Non-unital non-associative `R`-algebra `A` is defined by the combination
`[NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]`


## Tags

`CommSemiring`, ` Non-unital Power-associative algebra`
-/

universe u v w x

open Finset AddMonoidAlgebra

open BigOperators

namespace Polynomial

variable {R : Type u} [CommSemiring R] {p : R[X]} {S : Type v} {T : Type w} {a b : R}

section NonUnital

variable [AddCommMonoid S] [MulActionWithZero R S] [Pow S ℕ+] (p: ℕ+ →₀ R) (x : S)

/-- Scalar multiplication by a positive power. -/
def smul_ppow : ℕ+ → R → S := fun n r => r • x^n

/-- Evaluate a polynomial `p` in the scalar commutative semiring `R` with vanishing constant term at
an element `x` in the target object `S` with scalar multiplication by `R`. We allow any polynomial,
but get wrong answers when there are constant terms. -/
irreducible_def smnueval : S := p.sum (smul_ppow x)

theorem smnueval_eq_sum : smnueval p x = p.sum (smul_ppow x) := by
  rw [smnueval_def]

theorem smnueval_zero : smnueval (0 : ℕ+ →₀ R ) x = (0 : S) := by
  simp only [smnueval_eq_sum, Finsupp.sum_zero_index]

theorem smnueval_X : smnueval (Finsupp.single 1 1) x = x ^ (1 : ℕ+) := by
  simp only [smnueval_eq_sum, smul_ppow, zero_smul, Finsupp.sum_single_index, one_smul]

theorem smnueval_monomial (r : R) (n : ℕ+) : smnueval (Finsupp.single n r) x = r • x ^ n := by
  simp only [smnueval_eq_sum, smul_ppow, zero_smul, Finsupp.sum_single_index]

theorem smnueval_X_pow {n : ℕ+} : smnueval (Finsupp.single n (1 : R)) x = x ^ n := by
  rw [← one_smul R (x^n)]
  exact smnueval_monomial x 1 n

end NonUnital

section Unital

variable [AddCommMonoid S] [MulActionWithZero R S] [Pow S ℕ] (p q : R[X]) (r : R) (x : S)

/-- Scalar multiplication by a natural number power. -/
def smul_pow : ℕ → R → S := fun n r => r • x^n

/-- Evaluate a polynomial `p` in the scalar commutative semiring `R` at an element `x` in the target
power-associative `R`-algebra `S`. -/
irreducible_def smeval : S := p.sum (smul_pow x)

theorem smeval_eq_sum : p.smeval x = p.sum (smul_pow x) := by rw [smeval_def]

theorem smeval_zero : (0 : R[X]).smeval x = 0 := by
  simp only [smeval_eq_sum, smul_pow, sum_zero_index]

theorem smeval_C : (C r).smeval x = r • x^0 := by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_C_index]

theorem smeval_one : (1 : R[X]).smeval x = 1 • x^0 := by
  rw [← C_1, smeval_C]
  simp only [Nat.cast_one, one_smul]

theorem smeval_X : (X:R[X]).smeval x = x^1 := by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_X_index, one_smul]

theorem smeval_monomial (n : ℕ) : (monomial n r).smeval x = r • x ^ n := by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_monomial_index]

theorem smeval_X_pow {n : ℕ} : (X ^ n : R[X]).smeval x = x ^ n := by
  simp only [smeval_eq_sum, smul_pow, X_pow_eq_monomial, zero_smul, sum_monomial_index, one_smul]

theorem smeval_eq_eval (y : R) : p.smeval y = p.eval y := by
  rw [eval_eq_sum, smeval_eq_sum]
  simp only [smul_pow, smul_eq_mul]

end Unital

section NonUnitalPowAssoc

variable [NonUnitalNonAssocSemiring S] [Module R S] [IsScalarTower R S S] [SMulCommClass R S S]

variable [Pow S ℕ+] [PosPowAssoc S] (p: ℕ+ →₀ R) (x : S)

theorem _root_.zero_ppow : ∀(n : ℕ+), (0:S)^n = 0 := by  --use Nat.succPNat in exponents
  have h : ∀(k : ℕ), (0:S)^(Nat.succPNat k) = 0
    | 0 => by
      have h : Nat.succPNat 0 = 1 := by exact rfl
      rw [h, ppow_one]
    | (k+1) => by
      have h : Nat.succPNat (k+1) = 1 + Nat.succPNat k := by
        refine PNat.natPred_inj.mp ?_
        rw [Nat.natPred_succPNat, PNat.natPred, PNat.add_coe]
        exact (Nat.add_sub_self_left ↑1 ↑(Nat.succPNat k)).symm
      rw [h, ← mul_ppow, ppow_one, zero_mul]
  intro n
  rw [← PNat.succPNat_natPred n, h]

theorem smnueval_at_zero : smnueval p (0:S) = 0 := by
  simp only [smnueval_eq_sum, smul_ppow]
  simp_rw [zero_ppow]
  simp only [smul_zero, Finsupp.sum_zero]

-- smnueval_mul_X, smnuevalcomp, etc.

end NonUnitalPowAssoc

section UnitalPowAssoc

variable [NonAssocSemiring S] [Module R S] [IsScalarTower R S S] [SMulCommClass R S S]

variable [Pow S ℕ] [PowAssoc S]

variable (x : S) (p q : R[X])

theorem smeval_add_pow_assoc : (p + q).smeval x = p.smeval x + q.smeval x := by
  simp [smeval_eq_sum, smul_pow]
  refine sum_add_index p q (smul_pow x) ?_ ?_
  simp [smul_pow]
  simp [smul_pow, add_smul]

--theorem smeval_at_zero : p.smeval (0 : S) = (p.coeff 0) • (1 : S)  := by
--  simp only [smeval_eq_sum, smul_pow]
  --simp_rw [zero_pow_eq, mul_ite, zero_pow]
  --simp (config := { contextual := true }) only [mul_zero, mul_one, sum, Classical.not_not,
  --mem_support_iff, sum_ite_eq', ite_eq_left_iff, imp_true_iff, eq_self_iff_true]

theorem smeval_mul_X_pow_assoc : (p * X).smeval x = p.smeval x * x := by
    induction p using Polynomial.induction_on' with
  | h_add p q ph qh =>
    simp only [add_mul, smeval_add_pow_assoc, ph, qh]
  | h_monomial n a =>
    simp only [← monomial_one_one_eq_X, monomial_mul_monomial, smeval_monomial, mul_one, pow_succ',
      mul_assoc]
    rw [← mul_npow, smul_mul_assoc, npow_one]

-- smevalcomp, etc.

end UnitalPowAssoc

section Semiring

variable [Semiring S] [Algebra R S]

variable (x : S) (p q : R[X])

theorem smeval_add : (p + q).smeval x = p.smeval x + q.smeval x := by
  simp [smeval_eq_sum, smul_pow]
  refine sum_add_index p q (smul_pow x) ?_ ?_
  simp [smul_pow]
  simp [smul_pow, add_smul]

theorem smeval_mul_X : (p * X).smeval x = p.smeval x * x := by
    induction p using Polynomial.induction_on' with
  | h_add p q ph qh =>
    simp only [add_mul, smeval_add, ph, qh]
  | h_monomial n a =>
    simp only [← monomial_one_one_eq_X, monomial_mul_monomial, smeval_monomial, mul_one, pow_succ',
      mul_assoc, smul_mul_assoc]

theorem smeval_X_mul : (X * p).smeval x = x * p.smeval x := by
    induction p using Polynomial.induction_on' with
  | h_add p q ph qh =>
    simp only [smeval_add, ph, qh, mul_add]
  | h_monomial n a =>
    rw [← monomial_one_one_eq_X, monomial_mul_monomial, smeval_monomial]
    rw [one_mul, add_comm, pow_succ, ← mul_smul_comm, smeval_monomial]

theorem smeval_mul_X_pow : ∀(n : ℕ), (p * X^n).smeval x = p.smeval x * x^n
  | 0 => by
    simp only [pow_zero, mul_one]
  | n + 1 => by
    rw [pow_succ', ← mul_assoc, smeval_mul_X, smeval_mul_X_pow n, pow_succ', mul_assoc]

theorem smeval_X_pow_mul : ∀(n : ℕ), (X^n * p).smeval x = x^n * p.smeval x
  | 0 => by
    simp only [pow_zero, one_mul]
  | n + 1 => by
    rw [pow_succ, mul_assoc, smeval_X_mul, smeval_X_pow_mul n, ← mul_assoc, pow_succ]

theorem smeval_C_mul : (C a * p).smeval x = a • p.smeval x := by
  induction p using Polynomial.induction_on' with
  | h_add p q ph qh =>
    simp only [mul_add, smeval_add, ph, qh, smul_add]
  | h_monomial n b =>
    simp only [mul_assoc, C_mul_monomial, smeval_monomial, mul_smul]

theorem smeval_monomial_mul (r : R) (n : ℕ) :
    smeval (monomial n r * p) x = r • (x ^ n * p.smeval x) := by
  induction p using Polynomial.induction_on' with
  | h_add r s hr hs =>
    simp only [add_comp, hr, hs, smeval_add, add_mul]
    rw [← @C_mul_X_pow_eq_monomial, mul_assoc, smeval_C_mul, smeval_X_pow_mul, smeval_add]
  | h_monomial n a =>
    simp only [smeval_monomial, smeval_C_mul, smeval_X_pow_mul, smeval_monomial_mul,
      monomial_mul_monomial, pow_add, mul_smul, Algebra.mul_smul_comm]

theorem smeval_mul : (p * q).smeval x  = p.smeval x * q.smeval x := by
  induction p using Polynomial.induction_on' with
  | h_add r s hr hs =>
    simp [add_comp, hr, hs, smeval_add, add_mul]
  | h_monomial n a =>
    simp [smeval_monomial, smeval_C_mul, smeval_mul_X_pow, smeval_monomial_mul]

theorem smeval_pow : ∀(n : ℕ), (p^n).smeval x = (p.smeval x)^n
  | 0 => by
    simp only [pow_zero, smeval_one, one_smul]
  | n + 1 => by
    rw [pow_succ', smeval_mul, pow_succ', smeval_pow n]

theorem smeval_comp : (p.comp q).smeval x  = p.smeval (q.smeval x) := by
  induction p using Polynomial.induction_on' with
  | h_add r s hr hs =>
    simp [add_comp, hr, hs, smeval_add]
  | h_monomial n a =>
    simp [smeval_monomial, smeval_C_mul, smeval_pow]

end Semiring
