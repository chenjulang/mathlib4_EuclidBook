/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathlib.Tactic.FinCases
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.Algebra.Field.IsField
import Mathlib.Tactic.Abel

/-!

# Ideals over a ring

This file defines `Ideal R`, the type of (left) ideals over a ring `R`.
Note that over commutative rings, left ideals and two-sided ideals are equivalent.

## Implementation notes

`Ideal R` is implemented using `Submodule R R`, where `•` is interpreted as `*`.

## TODO

Support right ideals, and two-sided ideals over non-commutative rings.
-/


universe u v w

variable {α : Type u} {β : Type v}

open Set Function

open Pointwise

/-- A (left) ideal in a semiring `R` is an additive submonoid `s` such that
`a * b ∈ s` whenever `b ∈ s`. If `R` is a ring, then `s` is an additive subgroup. -/
abbrev Ideal (R : Type u) [Semiring R] :=
  Submodule R R

/-- A ring is a principal ideal ring if all (left) ideals are principal. -/
@[mk_iff]
class IsPrincipalIdealRing (R : Type u) [Semiring R] : Prop where
  principal : ∀ S : Ideal R, S.IsPrincipal

attribute [instance] IsPrincipalIdealRing.principal

section Semiring

namespace Ideal

variable [Semiring α] (I : Ideal α) {a b : α}

protected theorem zero_mem : (0 : α) ∈ I :=
  Submodule.zero_mem I

protected theorem add_mem : a ∈ I → b ∈ I → a + b ∈ I :=
  Submodule.add_mem I

variable (a)

theorem mul_mem_left : b ∈ I → a * b ∈ I :=
  Submodule.smul_mem I a

variable {a}

@[ext]
theorem ext {I J : Ideal α} (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
  Submodule.ext h

theorem sum_mem (I : Ideal α) {ι : Type*} {t : Finset ι} {f : ι → α} :
    (∀ c ∈ t, f c ∈ I) → (∑ i ∈ t, f i) ∈ I :=
  Submodule.sum_mem I

theorem eq_top_of_unit_mem (x y : α) (hx : x ∈ I) (h : y * x = 1) : I = ⊤ :=
  eq_top_iff.2 fun z _ =>
    calc
      z * y * x ∈ I := I.mul_mem_left _ hx
      _ = z * (y * x) := mul_assoc z y x
      _ = z := by rw [h, mul_one]

theorem eq_top_of_isUnit_mem {x} (hx : x ∈ I) (h : IsUnit x) : I = ⊤ :=
  let ⟨y, hy⟩ := h.exists_left_inv
  eq_top_of_unit_mem I x y hx hy

theorem eq_top_iff_one : I = ⊤ ↔ (1 : α) ∈ I :=
  ⟨by rintro rfl; trivial, fun h => eq_top_of_unit_mem _ _ 1 h (by simp)⟩

theorem ne_top_iff_one : I ≠ ⊤ ↔ (1 : α) ∉ I :=
  not_congr I.eq_top_iff_one

@[simp]
theorem unit_mul_mem_iff_mem {x y : α} (hy : IsUnit y) : y * x ∈ I ↔ x ∈ I := by
  refine ⟨fun h => ?_, fun h => I.mul_mem_left y h⟩
  obtain ⟨y', hy'⟩ := hy.exists_left_inv
  have := I.mul_mem_left y' h
  rwa [← mul_assoc, hy', one_mul] at this

/-- The ideal generated by a subset of a ring -/
def span (s : Set α) : Ideal α :=
  Submodule.span α s

@[simp]
theorem submodule_span_eq {s : Set α} : Submodule.span α s = Ideal.span s :=
  rfl

@[simp]
theorem span_empty : span (∅ : Set α) = ⊥ :=
  Submodule.span_empty

@[simp]
theorem span_univ : span (Set.univ : Set α) = ⊤ :=
  Submodule.span_univ

theorem span_union (s t : Set α) : span (s ∪ t) = span s ⊔ span t :=
  Submodule.span_union _ _

theorem span_iUnion {ι} (s : ι → Set α) : span (⋃ i, s i) = ⨆ i, span (s i) :=
  Submodule.span_iUnion _

theorem mem_span {s : Set α} (x) : x ∈ span s ↔ ∀ p : Ideal α, s ⊆ p → x ∈ p :=
  mem_iInter₂

theorem subset_span {s : Set α} : s ⊆ span s :=
  Submodule.subset_span

theorem span_le {s : Set α} {I} : span s ≤ I ↔ s ⊆ I :=
  Submodule.span_le

theorem span_mono {s t : Set α} : s ⊆ t → span s ≤ span t :=
  Submodule.span_mono

@[simp]
theorem span_eq : span (I : Set α) = I :=
  Submodule.span_eq _

@[simp]
theorem span_singleton_one : span ({1} : Set α) = ⊤ :=
  (eq_top_iff_one _).2 <| subset_span <| mem_singleton _

theorem isCompactElement_top : CompleteLattice.IsCompactElement (⊤ : Ideal α) := by
  simpa only [← span_singleton_one] using Submodule.singleton_span_isCompactElement 1

theorem mem_span_insert {s : Set α} {x y} :
    x ∈ span (insert y s) ↔ ∃ a, ∃ z ∈ span s, x = a * y + z :=
  Submodule.mem_span_insert

theorem mem_span_singleton' {x y : α} : x ∈ span ({y} : Set α) ↔ ∃ a, a * y = x :=
  Submodule.mem_span_singleton

theorem span_singleton_le_iff_mem {x : α} : span {x} ≤ I ↔ x ∈ I :=
  Submodule.span_singleton_le_iff_mem _ _

theorem span_singleton_mul_left_unit {a : α} (h2 : IsUnit a) (x : α) :
    span ({a * x} : Set α) = span {x} := by
  apply le_antisymm <;> rw [span_singleton_le_iff_mem, mem_span_singleton']
  exacts [⟨a, rfl⟩, ⟨_, h2.unit.inv_mul_cancel_left x⟩]

theorem span_insert (x) (s : Set α) : span (insert x s) = span ({x} : Set α) ⊔ span s :=
  Submodule.span_insert x s

theorem span_eq_bot {s : Set α} : span s = ⊥ ↔ ∀ x ∈ s, (x : α) = 0 :=
  Submodule.span_eq_bot

@[simp]
theorem span_singleton_eq_bot {x} : span ({x} : Set α) = ⊥ ↔ x = 0 :=
  Submodule.span_singleton_eq_bot

theorem span_singleton_ne_top {α : Type*} [CommSemiring α] {x : α} (hx : ¬IsUnit x) :
    Ideal.span ({x} : Set α) ≠ ⊤ :=
  (Ideal.ne_top_iff_one _).mpr fun h1 =>
    let ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp h1
    hx ⟨⟨x, y, mul_comm y x ▸ hy, hy⟩, rfl⟩

@[simp]
theorem span_zero : span (0 : Set α) = ⊥ := by rw [← Set.singleton_zero, span_singleton_eq_bot]

@[simp]
theorem span_one : span (1 : Set α) = ⊤ := by rw [← Set.singleton_one, span_singleton_one]

theorem span_eq_top_iff_finite (s : Set α) :
    span s = ⊤ ↔ ∃ s' : Finset α, ↑s' ⊆ s ∧ span (s' : Set α) = ⊤ := by
  simp_rw [eq_top_iff_one]
  exact ⟨Submodule.mem_span_finite_of_mem_span, fun ⟨s', h₁, h₂⟩ => span_mono h₁ h₂⟩

theorem mem_span_singleton_sup {S : Type*} [CommSemiring S] {x y : S} {I : Ideal S} :
    x ∈ Ideal.span {y} ⊔ I ↔ ∃ a : S, ∃ b ∈ I, a * y + b = x := by
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨ya, hya, b, hb, rfl⟩
    obtain ⟨a, rfl⟩ := mem_span_singleton'.mp hya
    exact ⟨a, b, hb, rfl⟩
  · rintro ⟨a, b, hb, rfl⟩
    exact ⟨a * y, Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩, b, hb, rfl⟩

/-- The ideal generated by an arbitrary binary relation.
-/
def ofRel (r : α → α → Prop) : Ideal α :=
  Submodule.span α { x | ∃ a b, r a b ∧ x + b = a }

/-- An ideal `P` of a ring `R` is prime if `P ≠ R` and `xy ∈ P → x ∈ P ∨ y ∈ P` -/
class IsPrime (I : Ideal α) : Prop where
  /-- The prime ideal is not the entire ring. -/
  ne_top' : I ≠ ⊤
  /-- If a product lies in the prime ideal, then at least one element lies in the prime ideal. -/
  mem_or_mem' : ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I

theorem isPrime_iff {I : Ideal α} : IsPrime I ↔ I ≠ ⊤ ∧ ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

theorem IsPrime.ne_top {I : Ideal α} (hI : I.IsPrime) : I ≠ ⊤ :=
  hI.1

theorem IsPrime.mem_or_mem {I : Ideal α} (hI : I.IsPrime) {x y : α} : x * y ∈ I → x ∈ I ∨ y ∈ I :=
  hI.2

theorem IsPrime.mem_or_mem_of_mul_eq_zero {I : Ideal α} (hI : I.IsPrime) {x y : α} (h : x * y = 0) :
    x ∈ I ∨ y ∈ I :=
  hI.mem_or_mem (h.symm ▸ I.zero_mem)

theorem IsPrime.mem_of_pow_mem {I : Ideal α} (hI : I.IsPrime) {r : α} (n : ℕ) (H : r ^ n ∈ I) :
    r ∈ I := by
  induction n with
  | zero =>
    rw [pow_zero] at H
    exact (mt (eq_top_iff_one _).2 hI.1).elim H
  | succ n ih =>
    rw [pow_succ] at H
    exact Or.casesOn (hI.mem_or_mem H) ih id

theorem not_isPrime_iff {I : Ideal α} :
    ¬I.IsPrime ↔ I = ⊤ ∨ ∃ (x : α) (_hx : x ∉ I) (y : α) (_hy : y ∉ I), x * y ∈ I := by
  simp_rw [Ideal.isPrime_iff, not_and_or, Ne, Classical.not_not, not_forall, not_or]
  exact
    or_congr Iff.rfl
      ⟨fun ⟨x, y, hxy, hx, hy⟩ => ⟨x, hx, y, hy, hxy⟩, fun ⟨x, hx, y, hy, hxy⟩ =>
        ⟨x, y, hxy, hx, hy⟩⟩

theorem zero_ne_one_of_proper {I : Ideal α} (h : I ≠ ⊤) : (0 : α) ≠ 1 := fun hz =>
  I.ne_top_iff_one.1 h <| hz ▸ I.zero_mem

theorem bot_prime [IsDomain α] : (⊥ : Ideal α).IsPrime :=
  ⟨fun h => one_ne_zero (α := α) (by rwa [Ideal.eq_top_iff_one, Submodule.mem_bot] at h), fun h =>
    mul_eq_zero.mp (by simpa only [Submodule.mem_bot] using h)⟩

/-- An ideal is maximal if it is maximal in the collection of proper ideals. -/
class IsMaximal (I : Ideal α) : Prop where
  /-- The maximal ideal is a coatom in the ordering on ideals; that is, it is not the entire ring,
  and there are no other proper ideals strictly containing it. -/
  out : IsCoatom I

theorem isMaximal_def {I : Ideal α} : I.IsMaximal ↔ IsCoatom I :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem IsMaximal.ne_top {I : Ideal α} (h : I.IsMaximal) : I ≠ ⊤ :=
  (isMaximal_def.1 h).1

theorem isMaximal_iff {I : Ideal α} :
    I.IsMaximal ↔ (1 : α) ∉ I ∧ ∀ (J : Ideal α) (x), I ≤ J → x ∉ I → x ∈ J → (1 : α) ∈ J :=
  isMaximal_def.trans <|
    and_congr I.ne_top_iff_one <|
      forall_congr' fun J => by
        rw [lt_iff_le_not_le]
        exact
          ⟨fun H x h hx₁ hx₂ => J.eq_top_iff_one.1 <| H ⟨h, not_subset.2 ⟨_, hx₂, hx₁⟩⟩,
            fun H ⟨h₁, h₂⟩ =>
            let ⟨x, xJ, xI⟩ := not_subset.1 h₂
            J.eq_top_iff_one.2 <| H x h₁ xI xJ⟩

theorem IsMaximal.eq_of_le {I J : Ideal α} (hI : I.IsMaximal) (hJ : J ≠ ⊤) (IJ : I ≤ J) : I = J :=
  eq_iff_le_not_lt.2 ⟨IJ, fun h => hJ (hI.1.2 _ h)⟩

instance : IsCoatomic (Ideal α) := by
  apply CompleteLattice.coatomic_of_top_compact
  rw [← span_singleton_one]
  exact Submodule.singleton_span_isCompactElement 1

theorem IsMaximal.coprime_of_ne {M M' : Ideal α} (hM : M.IsMaximal) (hM' : M'.IsMaximal)
    (hne : M ≠ M') : M ⊔ M' = ⊤ := by
  contrapose! hne with h
  exact hM.eq_of_le hM'.ne_top (le_sup_left.trans_eq (hM'.eq_of_le h le_sup_right).symm)

/-- **Krull's theorem**: if `I` is an ideal that is not the whole ring, then it is included in some
    maximal ideal. -/
theorem exists_le_maximal (I : Ideal α) (hI : I ≠ ⊤) : ∃ M : Ideal α, M.IsMaximal ∧ I ≤ M :=
  let ⟨m, hm⟩ := (eq_top_or_exists_le_coatom I).resolve_left hI
  ⟨m, ⟨⟨hm.1⟩, hm.2⟩⟩

variable (α)

/-- Krull's theorem: a nontrivial ring has a maximal ideal. -/
theorem exists_maximal [Nontrivial α] : ∃ M : Ideal α, M.IsMaximal :=
  let ⟨I, ⟨hI, _⟩⟩ := exists_le_maximal (⊥ : Ideal α) bot_ne_top
  ⟨I, hI⟩

variable {α}

instance [Nontrivial α] : Nontrivial (Ideal α) := by
  rcases@exists_maximal α _ _ with ⟨M, hM, _⟩
  exact nontrivial_of_ne M ⊤ hM

/-- If P is not properly contained in any maximal ideal then it is not properly contained
  in any proper ideal -/
theorem maximal_of_no_maximal {P : Ideal α}
    (hmax : ∀ m : Ideal α, P < m → ¬IsMaximal m) (J : Ideal α) (hPJ : P < J) : J = ⊤ := by
  by_contra hnonmax
  rcases exists_le_maximal J hnonmax with ⟨M, hM1, hM2⟩
  exact hmax M (lt_of_lt_of_le hPJ hM2) hM1

theorem span_pair_comm {x y : α} : (span {x, y} : Ideal α) = span {y, x} := by
  simp only [span_insert, sup_comm]

theorem mem_span_pair {x y z : α} : z ∈ span ({x, y} : Set α) ↔ ∃ a b, a * x + b * y = z :=
  Submodule.mem_span_pair

@[simp]
theorem span_pair_add_mul_left {R : Type u} [CommRing R] {x y : R} (z : R) :
    (span {x + y * z, y} : Ideal R) = span {x, y} := by
  ext
  rw [mem_span_pair, mem_span_pair]
  exact
    ⟨fun ⟨a, b, h⟩ =>
      ⟨a, b + a * z, by
        rw [← h]
        ring1⟩,
      fun ⟨a, b, h⟩ =>
      ⟨a, b - a * z, by
        rw [← h]
        ring1⟩⟩

@[simp]
theorem span_pair_add_mul_right {R : Type u} [CommRing R] {x y : R} (z : R) :
    (span {x, y + x * z} : Ideal R) = span {x, y} := by
  rw [span_pair_comm, span_pair_add_mul_left, span_pair_comm]

theorem IsMaximal.exists_inv {I : Ideal α} (hI : I.IsMaximal) {x} (hx : x ∉ I) :
    ∃ y, ∃ i ∈ I, y * x + i = 1 := by
  cases' isMaximal_iff.1 hI with H₁ H₂
  rcases mem_span_insert.1
      (H₂ (span (insert x I)) x (Set.Subset.trans (subset_insert _ _) subset_span) hx
        (subset_span (mem_insert _ _))) with
    ⟨y, z, hz, hy⟩
  refine ⟨y, z, ?_, hy.symm⟩
  rwa [← span_eq I]

section Lattice

variable {R : Type u} [Semiring R]

-- Porting note: is this the right approach? or is there a better way to prove? (next 4 decls)
theorem mem_sup_left {S T : Ideal R} : ∀ {x : R}, x ∈ S → x ∈ S ⊔ T :=
  @le_sup_left _ _ S T

theorem mem_sup_right {S T : Ideal R} : ∀ {x : R}, x ∈ T → x ∈ S ⊔ T :=
  @le_sup_right _ _ S T

theorem mem_iSup_of_mem {ι : Sort*} {S : ι → Ideal R} (i : ι) : ∀ {x : R}, x ∈ S i → x ∈ iSup S :=
  @le_iSup _ _ _ S _

theorem mem_sSup_of_mem {S : Set (Ideal R)} {s : Ideal R} (hs : s ∈ S) :
    ∀ {x : R}, x ∈ s → x ∈ sSup S :=
  @le_sSup _ _ _ _ hs

theorem mem_sInf {s : Set (Ideal R)} {x : R} : x ∈ sInf s ↔ ∀ ⦃I⦄, I ∈ s → x ∈ I :=
  ⟨fun hx I his => hx I ⟨I, iInf_pos his⟩, fun H _I ⟨_J, hij⟩ => hij ▸ fun _S ⟨hj, hS⟩ => hS ▸ H hj⟩

@[simp 1001] -- Porting note: increased priority to appease `simpNF`
theorem mem_inf {I J : Ideal R} {x : R} : x ∈ I ⊓ J ↔ x ∈ I ∧ x ∈ J :=
  Iff.rfl

@[simp 1001] -- Porting note: increased priority to appease `simpNF`
theorem mem_iInf {ι : Sort*} {I : ι → Ideal R} {x : R} : x ∈ iInf I ↔ ∀ i, x ∈ I i :=
  Submodule.mem_iInf _

@[simp 1001] -- Porting note: increased priority to appease `simpNF`
theorem mem_bot {x : R} : x ∈ (⊥ : Ideal R) ↔ x = 0 :=
  Submodule.mem_bot _

end Lattice

section Pi

variable (ι : Type v)

/-- `I^n` as an ideal of `R^n`. -/
def pi : Ideal (ι → α) where
  carrier := { x | ∀ i, x i ∈ I }
  zero_mem' _i := I.zero_mem
  add_mem' ha hb i := I.add_mem (ha i) (hb i)
  smul_mem' a _b hb i := I.mul_mem_left (a i) (hb i)

theorem mem_pi (x : ι → α) : x ∈ I.pi ι ↔ ∀ i, x i ∈ I :=
  Iff.rfl

end Pi

theorem sInf_isPrime_of_isChain {s : Set (Ideal α)} (hs : s.Nonempty) (hs' : IsChain (· ≤ ·) s)
    (H : ∀ p ∈ s, Ideal.IsPrime p) : (sInf s).IsPrime :=
  ⟨fun e =>
    let ⟨x, hx⟩ := hs
    (H x hx).ne_top (eq_top_iff.mpr (e.symm.trans_le (sInf_le hx))),
    fun e =>
    or_iff_not_imp_left.mpr fun hx => by
      rw [Ideal.mem_sInf] at hx e ⊢
      push_neg at hx
      obtain ⟨I, hI, hI'⟩ := hx
      intro J hJ
      rcases hs'.total hI hJ with h | h
      · exact h (((H I hI).mem_or_mem (e hI)).resolve_left hI')
      · exact ((H J hJ).mem_or_mem (e hJ)).resolve_left fun x => hI' <| h x⟩

end Ideal

end Semiring

section CommSemiring

variable {a b : α}

-- A separate namespace definition is needed because the variables were historically in a different
-- order.
namespace Ideal

variable [CommSemiring α] (I : Ideal α)

@[simp]
theorem mul_unit_mem_iff_mem {x y : α} (hy : IsUnit y) : x * y ∈ I ↔ x ∈ I :=
  mul_comm y x ▸ unit_mul_mem_iff_mem I hy

theorem mem_span_singleton {x y : α} : x ∈ span ({y} : Set α) ↔ y ∣ x :=
  mem_span_singleton'.trans <| exists_congr fun _ => by rw [eq_comm, mul_comm]

theorem mem_span_singleton_self (x : α) : x ∈ span ({x} : Set α) :=
  mem_span_singleton.mpr dvd_rfl

theorem span_singleton_le_span_singleton {x y : α} :
    span ({x} : Set α) ≤ span ({y} : Set α) ↔ y ∣ x :=
  span_le.trans <| singleton_subset_iff.trans mem_span_singleton

theorem span_singleton_eq_span_singleton {α : Type u} [CommRing α] [IsDomain α] {x y : α} :
    span ({x} : Set α) = span ({y} : Set α) ↔ Associated x y := by
  rw [← dvd_dvd_iff_associated, le_antisymm_iff, and_comm]
  apply and_congr <;> rw [span_singleton_le_span_singleton]

theorem span_singleton_mul_right_unit {a : α} (h2 : IsUnit a) (x : α) :
    span ({x * a} : Set α) = span {x} := by rw [mul_comm, span_singleton_mul_left_unit h2]

@[simp]
theorem span_singleton_eq_top {x} : span ({x} : Set α) = ⊤ ↔ IsUnit x := by
  rw [isUnit_iff_dvd_one, ← span_singleton_le_span_singleton, span_singleton_one, eq_top_iff]

theorem span_singleton_prime {p : α} (hp : p ≠ 0) : IsPrime (span ({p} : Set α)) ↔ Prime p := by
  simp [isPrime_iff, Prime, span_singleton_eq_top, hp, mem_span_singleton]

theorem IsMaximal.isPrime {I : Ideal α} (H : I.IsMaximal) : I.IsPrime :=
  ⟨H.1.1, @fun x y hxy =>
    or_iff_not_imp_left.2 fun hx => by
      let J : Ideal α := Submodule.span α (insert x ↑I)
      have IJ : I ≤ J := Set.Subset.trans (subset_insert _ _) subset_span
      have xJ : x ∈ J := Ideal.subset_span (Set.mem_insert x I)
      cases' isMaximal_iff.1 H with _ oJ
      specialize oJ J x IJ hx xJ
      rcases Submodule.mem_span_insert.mp oJ with ⟨a, b, h, oe⟩
      obtain F : y * 1 = y * (a • x + b) := congr_arg (fun g : α => y * g) oe
      rw [← mul_one y, F, mul_add, mul_comm, smul_eq_mul, mul_assoc]
      refine Submodule.add_mem I (I.mul_mem_left a hxy) (Submodule.smul_mem I y ?_)
      rwa [Submodule.span_eq] at h⟩

-- see Note [lower instance priority]
instance (priority := 100) IsMaximal.isPrime' (I : Ideal α) : ∀ [_H : I.IsMaximal], I.IsPrime :=
  @IsMaximal.isPrime _ _ _

theorem span_singleton_lt_span_singleton [IsDomain α] {x y : α} :
    span ({x} : Set α) < span ({y} : Set α) ↔ DvdNotUnit y x := by
  rw [lt_iff_le_not_le, span_singleton_le_span_singleton, span_singleton_le_span_singleton,
    dvd_and_not_dvd_iff]

theorem factors_decreasing [IsDomain α] (b₁ b₂ : α) (h₁ : b₁ ≠ 0) (h₂ : ¬IsUnit b₂) :
    span ({b₁ * b₂} : Set α) < span {b₁} :=
  lt_of_le_not_le
    (Ideal.span_le.2 <| singleton_subset_iff.2 <| Ideal.mem_span_singleton.2 ⟨b₂, rfl⟩) fun h =>
    h₂ <| isUnit_of_dvd_one <|
        (mul_dvd_mul_iff_left h₁).1 <| by rwa [mul_one, ← Ideal.span_singleton_le_span_singleton]

variable (b)

theorem mul_mem_right (h : a ∈ I) : a * b ∈ I :=
  mul_comm b a ▸ I.mul_mem_left b h

variable {b}

theorem pow_mem_of_mem (ha : a ∈ I) (n : ℕ) (hn : 0 < n) : a ^ n ∈ I :=
  Nat.casesOn n (Not.elim (by decide))
    (fun m _hm => (pow_succ a m).symm ▸ I.mul_mem_left (a ^ m) ha) hn

theorem pow_mem_of_pow_mem {m n : ℕ} (ha : a ^ m ∈ I) (h : m ≤ n) : a ^ n ∈ I := by
  rw [← Nat.add_sub_of_le h, pow_add]
  exact I.mul_mem_right _ ha

theorem add_pow_mem_of_pow_mem_of_le {m n k : ℕ}
    (ha : a ^ m ∈ I) (hb : b ^ n ∈ I) (hk : m + n ≤ k + 1) :
    (a + b) ^ k ∈ I := by
  rw [add_pow]
  apply I.sum_mem
  intro c _
  apply mul_mem_right
  by_cases h : m ≤ c
  · exact I.mul_mem_right _ (I.pow_mem_of_pow_mem ha h)
  · refine I.mul_mem_left _ (I.pow_mem_of_pow_mem hb ?_)
    simp only [not_le, Nat.lt_iff_add_one_le] at h
    have hck : c ≤ k := by
      rw [← add_le_add_iff_right 1]
      exact le_trans h (le_trans (Nat.le_add_right _ _) hk)
    rw [Nat.le_sub_iff_add_le hck, ← add_le_add_iff_right 1]
    exact le_trans (by rwa [add_comm _ n, add_assoc, add_le_add_iff_left]) hk

theorem add_pow_add_pred_mem_of_pow_mem  {m n : ℕ}
    (ha : a ^ m ∈ I) (hb : b ^ n ∈ I) :
    (a + b) ^ (m + n - 1) ∈ I :=
  I.add_pow_mem_of_pow_mem_of_le ha hb <| by rw [← Nat.sub_le_iff_le_add]

theorem IsPrime.mul_mem_iff_mem_or_mem {I : Ideal α} (hI : I.IsPrime) :
    ∀ {x y : α}, x * y ∈ I ↔ x ∈ I ∨ y ∈ I := @fun x y =>
  ⟨hI.mem_or_mem, by
    rintro (h | h)
    exacts [I.mul_mem_right y h, I.mul_mem_left x h]⟩

theorem IsPrime.pow_mem_iff_mem {I : Ideal α} (hI : I.IsPrime) {r : α} (n : ℕ) (hn : 0 < n) :
    r ^ n ∈ I ↔ r ∈ I :=
  ⟨hI.mem_of_pow_mem n, fun hr => I.pow_mem_of_mem hr n hn⟩

theorem pow_multiset_sum_mem_span_pow [DecidableEq α] (s : Multiset α) (n : ℕ) :
    s.sum ^ (Multiset.card s * n + 1) ∈
    span ((s.map fun (x : α) ↦ x ^ (n + 1)).toFinset : Set α) := by
  induction' s using Multiset.induction_on with a s hs
  · simp
  simp only [Finset.coe_insert, Multiset.map_cons, Multiset.toFinset_cons, Multiset.sum_cons,
    Multiset.card_cons, add_pow]
  refine Submodule.sum_mem _ ?_
  intro c _hc
  rw [mem_span_insert]
  by_cases h : n + 1 ≤ c
  · refine ⟨a ^ (c - (n + 1)) * s.sum ^ ((Multiset.card s + 1) * n + 1 - c) *
      ((Multiset.card s + 1) * n + 1).choose c, 0, Submodule.zero_mem _, ?_⟩
    rw [mul_comm _ (a ^ (n + 1))]
    simp_rw [← mul_assoc]
    rw [← pow_add, add_zero, add_tsub_cancel_of_le h]
  · use 0
    simp_rw [zero_mul, zero_add]
    refine ⟨_, ?_, rfl⟩
    replace h : c ≤ n := Nat.lt_succ_iff.mp (not_le.mp h)
    have : (Multiset.card s + 1) * n + 1 - c = Multiset.card s * n + 1 + (n - c) := by
      rw [add_mul, one_mul, add_assoc, add_comm n 1, ← add_assoc, add_tsub_assoc_of_le h]
    rw [this, pow_add]
    simp_rw [mul_assoc, mul_comm (s.sum ^ (Multiset.card s * n + 1)), ← mul_assoc]
    exact mul_mem_left _ _ hs

theorem sum_pow_mem_span_pow {ι} (s : Finset ι) (f : ι → α) (n : ℕ) :
    (∑ i ∈ s, f i) ^ (s.card * n + 1) ∈ span ((fun i => f i ^ (n + 1)) '' s) := by
  classical
  simpa only [Multiset.card_map, Multiset.map_map, comp_apply, Multiset.toFinset_map,
    Finset.coe_image, Finset.val_toFinset] using pow_multiset_sum_mem_span_pow (s.1.map f) n

theorem span_pow_eq_top (s : Set α) (hs : span s = ⊤) (n : ℕ) :
    span ((fun (x : α) => x ^ n) '' s) = ⊤ := by
  rw [eq_top_iff_one]
  cases' n with n
  · obtain rfl | ⟨x, hx⟩ := eq_empty_or_nonempty s
    · rw [Set.image_empty, hs]
      trivial
    · exact subset_span ⟨_, hx, pow_zero _⟩
  rw [eq_top_iff_one, span, Finsupp.mem_span_iff_linearCombination] at hs
  rcases hs with ⟨f, hf⟩
  have hf : (f.support.sum fun a => f a * a) = 1 := hf -- Porting note: was `change ... at hf`
  have := sum_pow_mem_span_pow f.support (fun a => f a * a) n
  rw [hf, one_pow] at this
  refine span_le.mpr ?_ this
  rintro _ hx
  simp_rw [Set.mem_image] at hx
  rcases hx with ⟨x, _, rfl⟩
  have : span ({(x : α) ^ (n + 1)} : Set α) ≤ span ((fun x : α => x ^ (n + 1)) '' s) := by
    rw [span_le, Set.singleton_subset_iff]
    exact subset_span ⟨x, x.prop, rfl⟩
  refine this ?_
  rw [mul_pow, mem_span_singleton]
  exact ⟨f x ^ (n + 1), mul_comm _ _⟩

lemma isPrime_of_maximally_disjoint (I : Ideal α)
    (S : Submonoid α)
    (disjoint : Disjoint (I : Set α) S)
    (maximally_disjoint : ∀ (J : Ideal α), I < J → ¬ Disjoint (J : Set α) S) :
    I.IsPrime where
  ne_top' := by
    rintro rfl
    have : 1 ∈ (S : Set α) := S.one_mem
    aesop
  mem_or_mem' {x y} hxy := by
    by_contra! rid
    have hx := maximally_disjoint (I ⊔ span {x}) (Submodule.lt_sup_iff_not_mem.mpr rid.1)
    have hy := maximally_disjoint (I ⊔ span {y}) (Submodule.lt_sup_iff_not_mem.mpr rid.2)
    simp only [Set.not_disjoint_iff, mem_inter_iff, SetLike.mem_coe, Submodule.mem_sup,
      mem_span_singleton] at hx hy
    obtain ⟨s₁, ⟨i₁, hi₁, ⟨_, ⟨r₁, rfl⟩, hr₁⟩⟩, hs₁⟩ := hx
    obtain ⟨s₂, ⟨i₂, hi₂, ⟨_, ⟨r₂, rfl⟩, hr₂⟩⟩, hs₂⟩ := hy
    refine disjoint.ne_of_mem
      (I.add_mem (I.mul_mem_left (i₁ + x * r₁) hi₂) <| I.add_mem (I.mul_mem_right (y * r₂) hi₁) <|
        I.mul_mem_right (r₁ * r₂) hxy)
      (S.mul_mem hs₁ hs₂) ?_
    rw [← hr₁, ← hr₂]
    ring

end Ideal

end CommSemiring

section Ring

namespace Ideal

variable [Ring α] (I : Ideal α) {a b : α}

protected theorem neg_mem_iff : -a ∈ I ↔ a ∈ I :=
  Submodule.neg_mem_iff I

protected theorem add_mem_iff_left : b ∈ I → (a + b ∈ I ↔ a ∈ I) :=
  Submodule.add_mem_iff_left I

protected theorem add_mem_iff_right : a ∈ I → (a + b ∈ I ↔ b ∈ I) :=
  Submodule.add_mem_iff_right I

protected theorem sub_mem : a ∈ I → b ∈ I → a - b ∈ I :=
  Submodule.sub_mem I

theorem mem_span_insert' {s : Set α} {x y} : x ∈ span (insert y s) ↔ ∃ a, x + a * y ∈ span s :=
  Submodule.mem_span_insert'

@[simp]
theorem span_singleton_neg (x : α) : (span {-x} : Ideal α) = span {x} := by
  ext
  simp only [mem_span_singleton']
  exact ⟨fun ⟨y, h⟩ => ⟨-y, h ▸ neg_mul_comm y x⟩, fun ⟨y, h⟩ => ⟨-y, h ▸ neg_mul_neg y x⟩⟩

end Ideal

end Ring

section DivisionSemiring

variable {K : Type u} [DivisionSemiring K] (I : Ideal K)

namespace Ideal

/-- All ideals in a division (semi)ring are trivial. -/
theorem eq_bot_or_top : I = ⊥ ∨ I = ⊤ := by
  rw [or_iff_not_imp_right]
  change _ ≠ _ → _
  rw [Ideal.ne_top_iff_one]
  intro h1
  rw [eq_bot_iff]
  intro r hr
  by_cases H : r = 0; · simpa
  simpa [H, h1] using I.mul_mem_left r⁻¹ hr

variable (K) in
/-- A bijection between (left) ideals of a division ring and `{0, 1}`, sending `⊥` to `0`
and `⊤` to `1`. -/
def equivFinTwo [DecidableEq (Ideal K)] : Ideal K ≃ Fin 2 where
  toFun := fun I ↦ if I = ⊥ then 0 else 1
  invFun := ![⊥, ⊤]
  left_inv := fun I ↦ by rcases eq_bot_or_top I with rfl | rfl <;> simp
  right_inv := fun i ↦ by fin_cases i <;> simp

instance : Finite (Ideal K) := let _i := Classical.decEq (Ideal K); ⟨equivFinTwo K⟩

/-- Ideals of a `DivisionSemiring` are a simple order. Thanks to the way abbreviations work,
this automatically gives an `IsSimpleModule K` instance. -/
instance isSimpleOrder : IsSimpleOrder (Ideal K) :=
  ⟨eq_bot_or_top⟩

theorem eq_bot_of_prime [h : I.IsPrime] : I = ⊥ :=
  or_iff_not_imp_right.mp I.eq_bot_or_top h.1

theorem bot_isMaximal : IsMaximal (⊥ : Ideal K) :=
  ⟨⟨fun h => absurd ((eq_top_iff_one (⊤ : Ideal K)).mp rfl) (by rw [← h]; simp), fun I hI =>
      or_iff_not_imp_left.mp (eq_bot_or_top I) (ne_of_gt hI)⟩⟩

end Ideal

end DivisionSemiring

section CommRing

namespace Ideal

theorem mul_sub_mul_mem {R : Type*} [CommRing R] (I : Ideal R) {a b c d : R} (h1 : a - b ∈ I)
    (h2 : c - d ∈ I) : a * c - b * d ∈ I := by
  rw [show a * c - b * d = (a - b) * c + b * (c - d) by rw [sub_mul, mul_sub]; abel]
  exact I.add_mem (I.mul_mem_right _ h1) (I.mul_mem_left _ h2)

end Ideal

end CommRing

-- TODO: consider moving the lemmas below out of the `Ring` namespace since they are
-- about `CommSemiring`s.
namespace Ring

variable {R : Type*} [CommSemiring R]

theorem exists_not_isUnit_of_not_isField [Nontrivial R] (hf : ¬IsField R) :
    ∃ (x : R) (_hx : x ≠ (0 : R)), ¬IsUnit x := by
  have : ¬_ := fun h => hf ⟨exists_pair_ne R, mul_comm, h⟩
  simp_rw [isUnit_iff_exists_inv]
  push_neg at this ⊢
  obtain ⟨x, hx, not_unit⟩ := this
  exact ⟨x, hx, not_unit⟩

theorem not_isField_iff_exists_ideal_bot_lt_and_lt_top [Nontrivial R] :
    ¬IsField R ↔ ∃ I : Ideal R, ⊥ < I ∧ I < ⊤ := by
  constructor
  · intro h
    obtain ⟨x, nz, nu⟩ := exists_not_isUnit_of_not_isField h
    use Ideal.span {x}
    rw [bot_lt_iff_ne_bot, lt_top_iff_ne_top]
    exact ⟨mt Ideal.span_singleton_eq_bot.mp nz, mt Ideal.span_singleton_eq_top.mp nu⟩
  · rintro ⟨I, bot_lt, lt_top⟩ hf
    obtain ⟨x, mem, ne_zero⟩ := SetLike.exists_of_lt bot_lt
    rw [Submodule.mem_bot] at ne_zero
    obtain ⟨y, hy⟩ := hf.mul_inv_cancel ne_zero
    rw [lt_top_iff_ne_top, Ne, Ideal.eq_top_iff_one, ← hy] at lt_top
    exact lt_top (I.mul_mem_right _ mem)

theorem not_isField_iff_exists_prime [Nontrivial R] :
    ¬IsField R ↔ ∃ p : Ideal R, p ≠ ⊥ ∧ p.IsPrime :=
  not_isField_iff_exists_ideal_bot_lt_and_lt_top.trans
    ⟨fun ⟨I, bot_lt, lt_top⟩ =>
      let ⟨p, hp, le_p⟩ := I.exists_le_maximal (lt_top_iff_ne_top.mp lt_top)
      ⟨p, bot_lt_iff_ne_bot.mp (lt_of_lt_of_le bot_lt le_p), hp.isPrime⟩,
      fun ⟨p, ne_bot, Prime⟩ => ⟨p, bot_lt_iff_ne_bot.mpr ne_bot, lt_top_iff_ne_top.mpr Prime.1⟩⟩

/-- Also see `Ideal.isSimpleOrder` for the forward direction as an instance when `R` is a
division (semi)ring.

This result actually holds for all division semirings, but we lack the predicate to state it. -/
theorem isField_iff_isSimpleOrder_ideal : IsField R ↔ IsSimpleOrder (Ideal R) := by
  cases subsingleton_or_nontrivial R
  · exact
      ⟨fun h => (not_isField_of_subsingleton _ h).elim, fun h =>
        (false_of_nontrivial_of_subsingleton <| Ideal R).elim⟩
  rw [← not_iff_not, Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top, ← not_iff_not]
  push_neg
  simp_rw [lt_top_iff_ne_top, bot_lt_iff_ne_bot, ← or_iff_not_imp_left, not_ne_iff]
  exact ⟨fun h => ⟨h⟩, fun h => h.2⟩

/-- When a ring is not a field, the maximal ideals are nontrivial. -/
theorem ne_bot_of_isMaximal_of_not_isField [Nontrivial R] {M : Ideal R} (max : M.IsMaximal)
    (not_field : ¬IsField R) : M ≠ ⊥ := by
  rintro h
  rw [h] at max
  rcases max with ⟨⟨_h1, h2⟩⟩
  obtain ⟨I, hIbot, hItop⟩ := not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp not_field
  exact ne_of_lt hItop (h2 I hIbot)

end Ring

namespace Ideal

variable {R : Type u} [CommSemiring R] [Nontrivial R]

theorem bot_lt_of_maximal (M : Ideal R) [hm : M.IsMaximal] (non_field : ¬IsField R) : ⊥ < M := by
  rcases Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top.1 non_field with ⟨I, Ibot, Itop⟩
  constructor; · simp
  intro mle
  apply lt_irrefl (⊤ : Ideal R)
  have : M = ⊥ := eq_bot_iff.mpr mle
  rw [← this] at Ibot
  rwa [hm.1.2 I Ibot] at Itop

end Ideal

variable {a b : α}

/-- The set of non-invertible elements of a monoid. -/
def nonunits (α : Type u) [Monoid α] : Set α :=
  { a | ¬IsUnit a }

@[simp]
theorem mem_nonunits_iff [Monoid α] : a ∈ nonunits α ↔ ¬IsUnit a :=
  Iff.rfl

theorem mul_mem_nonunits_right [CommMonoid α] : b ∈ nonunits α → a * b ∈ nonunits α :=
  mt isUnit_of_mul_isUnit_right

theorem mul_mem_nonunits_left [CommMonoid α] : a ∈ nonunits α → a * b ∈ nonunits α :=
  mt isUnit_of_mul_isUnit_left

theorem zero_mem_nonunits [Semiring α] : 0 ∈ nonunits α ↔ (0 : α) ≠ 1 :=
  not_congr isUnit_zero_iff

@[simp 1001] -- increased priority to appease `simpNF`
theorem one_not_mem_nonunits [Monoid α] : (1 : α) ∉ nonunits α :=
  not_not_intro isUnit_one

theorem coe_subset_nonunits [Semiring α] {I : Ideal α} (h : I ≠ ⊤) : (I : Set α) ⊆ nonunits α :=
  fun _x hx hu => h <| I.eq_top_of_isUnit_mem hx hu

theorem exists_max_ideal_of_mem_nonunits [CommSemiring α] (h : a ∈ nonunits α) :
    ∃ I : Ideal α, I.IsMaximal ∧ a ∈ I := by
  have : Ideal.span ({a} : Set α) ≠ ⊤ := by
    intro H
    rw [Ideal.span_singleton_eq_top] at H
    contradiction
  rcases Ideal.exists_le_maximal _ this with ⟨I, Imax, H⟩
  use I, Imax
  apply H
  apply Ideal.subset_span
  exact Set.mem_singleton a
