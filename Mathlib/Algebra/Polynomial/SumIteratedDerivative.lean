/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Sum of iterated derivatives
-/

open Finset
open scoped Nat

namespace Polynomial

variable {R : Type*}

section Semiring

variable [Semiring R]

theorem sum_iterate_derivative_apply_of_lt {p : R[X]} {n : ℕ} (hn : p.natDegree < n) :
    ∑ i ∈ range (p.natDegree + 1), derivative^[i] p = ∑ i ∈ range n, derivative^[i] p := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [add_right_comm, sum_range_add _ _ m]
  convert (add_zero _).symm
  apply sum_eq_zero
  intro x _
  rw [add_comm, Function.iterate_add_apply, iterate_derivative_eq_zero (lt_add_one _),
    iterate_derivative_zero]

theorem sum_iterate_derivative_apply_of_le {p : R[X]} {n : ℕ} (hn : p.natDegree ≤ n) :
    ∑ i ∈ range (p.natDegree + 1), derivative^[i] p = ∑ i ∈ range (n + 1), derivative^[i] p :=
  sum_iterate_derivative_apply_of_lt (Nat.lt_add_one_iff.mpr hn)

/--
Sum of iterated derivatives of a polynomial, as a linear map

This definition does not allow different weights for the derivatives. It is likely that it could be
extended to allow them, but this was not needed for the initial use case (the integration by part
of the integral $I_i$ in the
[Lindemann-Weierstrass](https://en.wikipedia.org/wiki/Lindemann%E2%80%93Weierstrass_theorem)
theorem).
-/
noncomputable def sumIderiv : R[X] →ₗ[R] R[X] where
  toFun p := ∑ i ∈ range (p.natDegree + 1), derivative^[i] p
  map_add' p q := by
    dsimp only
    let x := max ((p + q).natDegree + 1) (max (p.natDegree + 1) (q.natDegree + 1))
    have hpq : (p + q).natDegree + 1 ≤ x := le_max_left _ _
    have hp : p.natDegree + 1 ≤ x := (le_max_left _ _).trans (le_max_right _ _)
    have hq : q.natDegree + 1 ≤ x := (le_max_right _ _).trans (le_max_right _ _)
    rw [Nat.add_one_le_iff] at hpq hp hq
    simp_rw [sum_iterate_derivative_apply_of_lt hpq, sum_iterate_derivative_apply_of_lt hp,
      sum_iterate_derivative_apply_of_lt hq, ← sum_add_distrib, iterate_map_add]
  map_smul' a p := by
    dsimp only
    simp_rw [RingHom.id_apply, sum_iterate_derivative_apply_of_le (natDegree_smul_le _ _),
      iterate_derivative_smul, smul_sum]

theorem sumIderiv_apply (p : R[X]) :
    sumIderiv p = ∑ i ∈ range (p.natDegree + 1), derivative^[i] p :=
  rfl

theorem sumIderiv_apply_of_lt {p : R[X]} {n : ℕ} (hn : p.natDegree < n) :
    sumIderiv p = ∑ i ∈ range n, derivative^[i] p :=
  sum_iterate_derivative_apply_of_lt hn

theorem sumIderiv_apply_of_le {p : R[X]} {n : ℕ} (hn : p.natDegree ≤ n) :
    sumIderiv p = ∑ i ∈ range (n + 1), derivative^[i] p :=
  sum_iterate_derivative_apply_of_le hn

theorem sumIderiv_C (a : R) : sumIderiv (C a) = C a := by
  rw [sumIderiv_apply, natDegree_C, zero_add, sum_range_one, Function.iterate_zero_apply]

@[simp]
theorem sumIderiv_map {S : Type*} [CommSemiring S] (p : R[X]) (f : R →+* S) :
    sumIderiv (p.map f) = (sumIderiv p).map f := by
  let n := max (p.map f).natDegree p.natDegree
  rw [sumIderiv_apply_of_le (le_max_left _ _ : _ ≤ n)]
  rw [sumIderiv_apply_of_le (le_max_right _ _ : _ ≤ n)]
  simp_rw [Polynomial.map_sum, iterate_derivative_map p f]

theorem sumIderiv_derivative (p : R[X]) : sumIderiv (derivative p) = derivative (sumIderiv p) := by
  rw [sumIderiv_apply_of_le ((natDegree_derivative_le p).trans tsub_le_self), sumIderiv_apply,
    derivative_sum]
  simp_rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']

theorem sumIderiv_eq_self_add (p : R[X]) : sumIderiv p = p + sumIderiv (derivative p) := by
  rw [sumIderiv_derivative, sumIderiv_apply, derivative_sum, sum_range_succ', sum_range_succ,
    add_comm, ← add_zero (Finset.sum _ _)]
  simp_rw [← Function.iterate_succ_apply' derivative, Nat.succ_eq_add_one,
    Function.iterate_zero_apply, iterate_derivative_eq_zero (Nat.lt_succ_self _)]

theorem iterate_derivative_eq_factorial_mul (p : R[X]) (k : ℕ) :
    derivative^[k] p = k ! •
      (∑ x ∈ (derivative^[k] p).support, (x + k).choose k • C (p.coeff (x + k)) * X ^ x) := by
  conv_lhs => rw [(derivative^[k] p).as_sum_support_C_mul_X_pow]
  rw [smul_sum]; congr; funext i
  calc
    C ((derivative^[k] p).coeff i) * X ^ i =
        C ((i + k).descFactorial k • p.coeff (i + k)) * X ^ i := by rw [coeff_iterate_derivative]
    _ = C ((k ! * (i + k).choose k) • p.coeff (i + k)) * X ^ i := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
    _ = (k ! * (i + k).choose k) • C (p.coeff (i + k)) * X ^ i := by rw [smul_C]
    _ = k ! • (i + k).choose k • C (p.coeff (i + k)) * X ^ i := by rw [mul_smul]
    _ = k ! • ((i + k).choose k • C (p.coeff (i + k)) * X ^ i) := by rw [smul_mul_assoc]

theorem exists_iterate_derivative_eq_factorial_mul (p : R[X]) (k : ℕ) :
    ∃ gp : R[X], gp.natDegree ≤ p.natDegree - k ∧ derivative^[k] p = k ! • gp := by
  use ∑ x ∈ (derivative^[k] p).support, (x + k).choose k • C (p.coeff (x + k)) * X ^ x
  constructor
  · refine (natDegree_sum_le _ _).trans ?_
    rw [fold_max_le]
    refine ⟨Nat.zero_le _, fun i hi => ?_⟩; dsimp only [Function.comp]
    replace hi := le_natDegree_of_mem_supp _ hi
    rw [smul_C]; refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_X_pow_le _).trans ?_
    refine hi.trans ?_
    exact natDegree_iterate_derivative _ _
  · exact iterate_derivative_eq_factorial_mul p k

end Semiring

section CommRing

variable [CommRing R] {A : Type*} [CommRing A] [Algebra R A]

theorem aeval_iterate_derivative_of_lt (p : R[X]) (q : ℕ) (r : A) {p' : A[X]}
    (hp : p.map (algebraMap R A) = (X - C r) ^ q * p') {k : ℕ} (hk : k < q) :
    aeval r (derivative^[k] p) = 0 := by
  have h (x) : (X - C r) ^ (q - (k - x)) = (X - C r) ^ 1 * (X - C r) ^ (q - (k - x) - 1) := by
    rw [← pow_add, add_tsub_cancel_of_le]
    rw [Nat.lt_iff_add_one_le] at hk
    exact (le_tsub_of_add_le_left hk).trans (tsub_le_tsub_left (tsub_le_self : _ ≤ k) _)
  rw [aeval_def, eval₂_eq_eval_map, ← iterate_derivative_map]
  simp_rw [hp, iterate_derivative_mul, iterate_derivative_X_sub_pow, ← smul_mul_assoc, smul_smul,
    h, ← mul_smul_comm, mul_assoc, ← mul_sum, eval_mul, pow_one, eval_sub, eval_X, eval_C, sub_self,
    zero_mul]

theorem aeval_iterate_derivative_self (p : R[X]) (q : ℕ) (r : A) {p' : A[X]}
    (hp : p.map (algebraMap R A) = (X - C r) ^ q * p') :
    aeval r (derivative^[q] p) = q ! • p'.eval r := by
  have h (x) (h : 1 ≤ x) (h' : x ≤ q) :
      (X - C r) ^ (q - (q - x)) = (X - C r) ^ 1 * (X - C r) ^ (q - (q - x) - 1) := by
    rw [← pow_add, add_tsub_cancel_of_le]
    rwa [tsub_tsub_cancel_of_le h']
  rw [aeval_def, eval₂_eq_eval_map, ← iterate_derivative_map]
  simp_rw [hp, iterate_derivative_mul, iterate_derivative_X_sub_pow, ← smul_mul_assoc, smul_smul]
  rw [sum_range_succ', Nat.choose_zero_right, one_mul, tsub_zero, Nat.descFactorial_self, tsub_self,
    pow_zero, smul_mul_assoc, one_mul, Function.iterate_zero_apply, eval_add, eval_smul]
  convert zero_add _
  rw [eval_finset_sum]
  apply sum_eq_zero
  intro x hx
  rw [h (x + 1) le_add_self (Nat.add_one_le_iff.mpr (mem_range.mp hx)), pow_one,
    eval_mul, eval_smul, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul,
    smul_zero, zero_mul]

variable (A)

theorem aeval_iterate_derivative_of_ge (p : R[X]) (q : ℕ) {k : ℕ} (hk : q ≤ k) :
    ∃ gp : R[X], gp.natDegree ≤ p.natDegree - k ∧
      ∀ r : A, aeval r (derivative^[k] p) = q ! • aeval r gp := by
  obtain ⟨p', p'_le, hp'⟩ := exists_iterate_derivative_eq_factorial_mul p k
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨((q + k).descFactorial k : R[X]) * p', (natDegree_C_mul_le _ _).trans p'_le, fun r => ?_⟩
  simp_rw [hp', nsmul_eq_mul, map_mul, map_natCast, ← mul_assoc, ← Nat.cast_mul,
    Nat.add_descFactorial_eq_ascFactorial, Nat.factorial_mul_ascFactorial]

theorem aeval_sumIderiv (p : R[X]) (q : ℕ) :
    ∃ (gp : R[X]) (gp_le : gp.natDegree ≤ p.natDegree - q),
      ∀ (r : A) {p' : A[X]}, p.map (algebraMap R A) = (X - C r) ^ q * p' →
        aeval r (sumIderiv p) = q ! • aeval r gp := by
  have h (k) :
      ∃ (gp : R[X]) (gp_le : gp.natDegree ≤ p.natDegree - q),
        ∀ (r : A) {p' : A[X]}, p.map (algebraMap R A) = (X - C r) ^ q * p' →
          aeval r (derivative^[k] p) = q ! • aeval r gp := by
    cases lt_or_ge k q with
    | inl hk =>
      use 0
      rw [natDegree_zero]
      use Nat.zero_le _
      intro r p' hp
      rw [map_zero, smul_zero, aeval_iterate_derivative_of_lt p q r hp hk]
    | inr hk =>
      obtain ⟨gp, gp_le, h⟩ := aeval_iterate_derivative_of_ge A p q hk
      exact ⟨gp, gp_le.trans (tsub_le_tsub_left hk _), fun r p' _ => h r⟩
  choose c h using h
  choose c_le hc using h
  refine ⟨(range (p.natDegree + 1)).sum c, ?_, ?_⟩
  · refine (natDegree_sum_le _ _).trans ?_
    rw [fold_max_le]
    exact ⟨Nat.zero_le _, fun i _ => c_le i⟩
  intro r p' hp
  rw [sumIderiv_apply, map_sum]; simp_rw [hc _ r hp, map_sum, smul_sum]

theorem aeval_sumIderiv' [Nontrivial A] [NoZeroDivisors A] (p : R[X]) {q : ℕ} (hq : 0 < q) :
    ∃ (gp : R[X]) (gp_le : gp.natDegree ≤ p.natDegree - q),
      ∀ (inj_amap : Function.Injective (algebraMap R A)) (r : A) {p' : A[X]},
        p.map (algebraMap R A) = (X - C r) ^ (q - 1) * p' →
        aeval r (sumIderiv p) = (q - 1)! • p'.eval r + q ! • aeval r gp := by
  rcases eq_or_ne p 0 with (rfl | p0)
  · use 0
    rw [natDegree_zero]
    use Nat.zero_le _
    intro _ r p' hp
    rw [map_zero, map_zero, smul_zero, add_zero]
    rw [Polynomial.map_zero] at hp
    replace hp := (mul_eq_zero.mp hp.symm).resolve_left ?_
    rw [hp, eval_zero, smul_zero]
    exact fun h => X_sub_C_ne_zero r (pow_eq_zero h)
  let c k := if hk : q ≤ k then (aeval_iterate_derivative_of_ge A p q hk).choose else 0
  have c_le (k) : (c k).natDegree ≤ p.natDegree - k := by
    dsimp only [c]
    split_ifs with h
    · exact (aeval_iterate_derivative_of_ge A p q h).choose_spec.1
    · rw [natDegree_zero]; exact Nat.zero_le _
  have hc (k) (hk : q ≤ k) : ∀ (r : A), aeval r (derivative^[k] p) = q ! • aeval r (c k) := by
    simp_rw [c, dif_pos hk]
    exact (aeval_iterate_derivative_of_ge A p q hk).choose_spec.2
  refine ⟨∑ x ∈ Ico q (p.natDegree + 1), c x, ?_, ?_⟩
  · refine (natDegree_sum_le _ _).trans ?_
    rw [fold_max_le]
    exact ⟨Nat.zero_le _, fun i hi => (c_le i).trans (tsub_le_tsub_left (mem_Ico.mp hi).1 _)⟩
  intro inj_amap r p' hp
  have : range (p.natDegree + 1) = range q ∪ Ico q (p.natDegree + 1) := by
    rw [range_eq_Ico, Ico_union_Ico_eq_Ico hq.le]
    have h := natDegree_map_le (algebraMap R A) p
    rw [congr_arg natDegree hp, natDegree_mul, natDegree_pow, natDegree_X_sub_C, mul_one,
      ← Nat.sub_add_comm (Nat.one_le_of_lt hq), tsub_le_iff_right] at h
    exact le_of_add_le_left h
    · exact pow_ne_zero _ (X_sub_C_ne_zero r)
    · rintro rfl
      rw [mul_zero, Polynomial.map_eq_zero_iff inj_amap] at hp
      exact p0 hp
  rw [← zero_add ((q - 1)! • p'.eval r)]
  rw [sumIderiv_apply, map_sum, map_sum, this]
  have : range q = range (q - 1 + 1) := by rw [tsub_add_cancel_of_le (Nat.one_le_of_lt hq)]
  rw [sum_union, this, sum_range_succ]
  congr 2
  · apply sum_eq_zero
    exact fun x hx => aeval_iterate_derivative_of_lt p _ r hp (mem_range.mp hx)
  · rw [← aeval_iterate_derivative_self _ _ _ hp]
  · rw [smul_sum, sum_congr rfl]
    intro k hk
    exact hc k (mem_Ico.mp hk).1 r
  · rw [range_eq_Ico, disjoint_iff_inter_eq_empty, eq_empty_iff_forall_not_mem]
    intro x hx
    rw [mem_inter, mem_Ico, mem_Ico] at hx
    exact hx.1.2.not_le hx.2.1

end CommRing

end Polynomial
