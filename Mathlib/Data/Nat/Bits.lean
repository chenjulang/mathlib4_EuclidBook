/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Nat
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Defs
import Mathlib.Tactic.Convert
import Mathlib.Tactic.GeneralizeProofs
import Mathlib.Tactic.Says

/-!
# Additional properties of binary recursion on `Nat`

This file documents additional properties of binary recursion,
which allows us to more easily work with operations which do depend
on the number of leading zeros in the binary representation of `n`.
For example, we can more easily work with `Nat.bits` and `Nat.size`.

See also: `Nat.bitwise`, `Nat.pow` (for various lemmas about `size` and `shiftLeft`/`shiftRight`),
and `Nat.digits`.
-/

-- Once we're in the `Nat` namespace, `xor` will inconveniently resolve to `Nat.xor`.
/-- `bxor` denotes the `xor` function i.e. the exclusive-or function on type `Bool`. -/
local notation "bxor" => xor

namespace Nat
universe u
variable {m n : ℕ}

/-- `boddDiv2 n` returns a 2-tuple of type `(Bool, Nat)` where the `Bool` value indicates whether
`n` is odd or not and the `Nat` value returns `⌊n/2⌋` -/
def boddDiv2 : ℕ → Bool × ℕ
  | 0 => (false, 0)
  | succ n =>
    match boddDiv2 n with
    | (false, m) => (true, m)
    | (true, m) => (false, succ m)

/-- `div2 n = ⌊n/2⌋` the greatest integer smaller than `n/2`-/
def div2 (n : ℕ) : ℕ := (boddDiv2 n).2

/-- `bodd n` returns `true` if `n` is odd -/
def bodd (n : ℕ) : Bool := (boddDiv2 n).1

@[simp] lemma bodd_zero : bodd 0 = false := rfl

@[simp] lemma bodd_one : bodd 1 = true := rfl

lemma bodd_two : bodd 2 = false := rfl

@[simp]
lemma bodd_succ (n : ℕ) : bodd (succ n) = not (bodd n) := by
  simp only [bodd, boddDiv2]
  let ⟨b,m⟩ := boddDiv2 n
  cases b <;> rfl

@[simp]
lemma bodd_add (m n : ℕ) : bodd (m + n) = bxor (bodd m) (bodd n) := by
  induction n
  case zero => simp
  case succ n ih => simp [← Nat.add_assoc, Bool.xor_not, ih]

@[simp]
lemma bodd_mul (m n : ℕ) : bodd (m * n) = (bodd m && bodd n) := by
  induction n with
  | zero => simp
  | succ n IH =>
    simp only [mul_succ, bodd_add, IH, bodd_succ]
    cases bodd m <;> cases bodd n <;> rfl

lemma mod_two_of_bodd (n : ℕ) : n % 2 = (bodd n).toNat := by
  have := congr_arg bodd (mod_add_div n 2)
  simp? [not] at this says
    simp only [bodd_add, bodd_mul, bodd_succ, not, bodd_zero, Bool.false_and, Bool.bne_false]
      at this
  have _ : ∀ b, and false b = false := by
    intro b
    cases b <;> rfl
  have _ : ∀ b, bxor b false = b := by
    intro b
    cases b <;> rfl
  rw [← this]
  rcases mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> rfl

@[simp] lemma div2_zero : div2 0 = 0 := rfl

@[simp] lemma div2_one : div2 1 = 0 := rfl

lemma div2_two : div2 2 = 1 := rfl

@[simp]
lemma div2_succ (n : ℕ) : div2 (n + 1) = cond (bodd n) (succ (div2 n)) (div2 n) := by
  simp only [bodd, boddDiv2, div2]
  rcases boddDiv2 n with ⟨_|_, _⟩ <;> simp

attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.mul_comm Nat.mul_assoc

lemma bodd_add_div2 : ∀ n, (bodd n).toNat + 2 * div2 n = n
  | 0 => rfl
  | succ n => by
    simp only [bodd_succ, Bool.cond_not, div2_succ, Nat.mul_comm]
    refine Eq.trans ?_ (congr_arg succ (bodd_add_div2 n))
    cases bodd n
    · simp
    · simp; omega

lemma div2_val (n) : div2 n = n / 2 := by
  refine Nat.eq_of_mul_eq_mul_left (by decide)
    (Nat.add_left_cancel (Eq.trans ?_ (Nat.mod_add_div n 2).symm))
  rw [mod_two_of_bodd, bodd_add_div2]

/-- `bit b` appends the digit `b` to the binary representation of its natural number input. -/
def bit (b : Bool) : ℕ → ℕ := cond b (2 * · + 1) (2 * ·)

lemma bit_val (b n) : bit b n = 2 * n + b.toNat := by
  cases b <;> rfl

lemma bit_decomp (n : Nat) : bit (bodd n) (div2 n) = n :=
  (bit_val _ _).trans <| (Nat.add_comm _ _).trans <| bodd_add_div2 _

theorem shiftRight_one (n) : n >>> 1 = n / 2 := rfl

@[simp]
theorem bit_decide_mod_two_eq_one_shiftRight_one (n : Nat) : bit (n % 2 = 1) (n >>> 1) = n := by
  simp only [bit, shiftRight_one]
  cases mod_two_eq_zero_or_one n with | _ h => simpa [h] using Nat.div_add_mod n 2

theorem bit_testBit_zero_shiftRight_one (n : Nat) : bit (n.testBit 0) (n >>> 1) = n := by
  simp

/-- For a predicate `motive : Nat → Sort*`, if instances can be
  constructed for natural numbers of the form `bit b n`,
  they can be constructed for any given natural number. -/
@[inline]
def bitCasesOn {motive : Nat → Sort u} (n) (h : ∀ b n, motive (bit b n)) : motive n :=
  -- `1 &&& n != 0` is faster than `n.testBit 0`. This may change when we have faster `testBit`.
  let x := h (1 &&& n != 0) (n >>> 1)
  -- `congrArg motive _ ▸ x` is defeq to `x` in non-dependent case
  congrArg motive n.bit_testBit_zero_shiftRight_one ▸ x

lemma bit_zero : bit false 0 = 0 :=
  rfl

/-- `shiftLeft' b m n` performs a left shift of `m` `n` times
 and adds the bit `b` as the least significant bit each time.
 Returns the corresponding natural number -/
def shiftLeft' (b : Bool) (m : ℕ) : ℕ → ℕ
  | 0 => m
  | n + 1 => bit b (shiftLeft' b m n)

@[simp]
lemma shiftLeft'_false : ∀ n, shiftLeft' false m n = m <<< n
  | 0 => rfl
  | n + 1 => by
    have : 2 * (m * 2^n) = 2^(n+1)*m := by
      rw [Nat.mul_comm, Nat.mul_assoc, ← Nat.pow_succ]; simp
    simp [shiftLeft_eq, shiftLeft', bit_val, shiftLeft'_false, this]

/-- Lean takes the unprimed name for `Nat.shiftLeft_eq m n : m <<< n = m * 2 ^ n`. -/
@[simp] lemma shiftLeft_eq' (m n : Nat) : shiftLeft m n = m <<< n := rfl
@[simp] lemma shiftRight_eq (m n : Nat) : shiftRight m n = m >>> n := rfl

lemma binaryRec_decreasing (h : n ≠ 0) : div2 n < n := by
  rw [div2_val]
  apply (div_lt_iff_lt_mul <| succ_pos 1).2
  have := Nat.mul_lt_mul_of_pos_left (lt_succ_self 1)
    (lt_of_le_of_ne n.zero_le h.symm)
  rwa [Nat.mul_one] at this

/-- A recursion principle for `bit` representations of natural numbers.
  For a predicate `motive : Nat → Sort*`, if instances can be
  constructed for natural numbers of the form `bit b n`,
  they can be constructed for all natural numbers. -/
@[elab_as_elim, specialize]
def binaryRec {motive : Nat → Sort u} (z : motive 0) (f : ∀ b n, motive n → motive (bit b n))
    (n : Nat) : motive n :=
  if n0 : n = 0 then congrArg motive n0 ▸ z
  else
    let x := f (1 &&& n != 0) (n >>> 1) (binaryRec z f (n >>> 1))
    congrArg motive n.bit_testBit_zero_shiftRight_one ▸ x
decreasing_by exact bitwise_rec_lemma n0

/-- `size n` : Returns the size of a natural number in
bits i.e. the length of its binary representation -/
def size : ℕ → ℕ :=
  binaryRec 0 fun _ _ => succ

/-- `bits n` returns a list of Bools which correspond to the binary representation of n, where
    the head of the list represents the least significant bit -/
def bits : ℕ → List Bool :=
  binaryRec [] fun b _ IH => b :: IH

/-- `ldiff a b` performs bitwise set difference. For each corresponding
  pair of bits taken as booleans, say `aᵢ` and `bᵢ`, it applies the
  boolean operation `aᵢ ∧ ¬bᵢ` to obtain the `iᵗʰ` bit of the result. -/
def ldiff : ℕ → ℕ → ℕ :=
  bitwise fun a b => a && not b

@[simp]
lemma binaryRec_zero {motive : Nat → Sort u}
    (z : motive 0) (f : ∀ b n, motive n → motive (bit b n)) :
    binaryRec z f 0 = z := by
  rw [binaryRec]
  rfl

@[simp]
lemma binaryRec_one {C : Nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) :
    binaryRec (motive := C) z f 1 = f true 0 z := by
  rw [binaryRec]
  simp only [succ_ne_self, ↓reduceDIte, reduceShiftRight, binaryRec_zero]
  rfl

/-! bitwise ops -/

lemma bodd_bit (b n) : bodd (bit b n) = b := by
  rw [bit_val]
  simp only [Nat.mul_comm, Nat.add_comm, bodd_add, bodd_mul, bodd_succ, bodd_zero, Bool.not_false,
    Bool.not_true, Bool.and_false, Bool.xor_false]
  cases b <;> cases bodd n <;> rfl

lemma div2_bit (b n) : div2 (bit b n) = n := by
  rw [bit_val, div2_val, Nat.add_comm, add_mul_div_left, div_eq_of_lt, Nat.zero_add]
  <;> cases b
  <;> decide

lemma shiftLeft'_add (b m n) : ∀ k, shiftLeft' b m (n + k) = shiftLeft' b (shiftLeft' b m n) k
  | 0 => rfl
  | k + 1 => congr_arg (bit b) (shiftLeft'_add b m n k)

lemma shiftLeft'_sub (b m) : ∀ {n k}, k ≤ n → shiftLeft' b m (n - k) = (shiftLeft' b m n) >>> k
  | _, 0, _ => rfl
  | n + 1, k + 1, h => by
    rw [succ_sub_succ_eq_sub, shiftLeft', Nat.add_comm, shiftRight_add]
    simp only [shiftLeft'_sub, Nat.le_of_succ_le_succ h, shiftRight_succ, shiftRight_zero]
    simp [← div2_val, div2_bit]

lemma shiftLeft_sub : ∀ (m : Nat) {n k}, k ≤ n → m <<< (n - k) = (m <<< n) >>> k :=
  fun _ _ _ hk => by simp only [← shiftLeft'_false, shiftLeft'_sub false _ hk]

-- Not a `simp` lemma, as later `simp` will be able to prove this.
lemma testBit_bit_zero (b n) : testBit (bit b n) 0 = b := by
  rw [testBit, bit]
  cases b
  · simp [← Nat.mul_two]
  · simp [← Nat.mul_two]

lemma bodd_eq_one_and_ne_zero : ∀ n, bodd n = (1 &&& n != 0)
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by simpa using bodd_eq_one_and_ne_zero n

lemma testBit_bit_succ (m b n) : testBit (bit b n) (succ m) = testBit n m := by
  have : bodd (((bit b n) >>> 1) >>> m) = bodd (n >>> m) := by
    simp only [shiftRight_eq_div_pow]
    simp [← div2_val, div2_bit]
  rw [← shiftRight_add, Nat.add_comm] at this
  simp only [bodd_eq_one_and_ne_zero] at this
  exact this

/-! ### `boddDiv2_eq` and `bodd` -/


@[simp]
theorem boddDiv2_eq (n : ℕ) : boddDiv2 n = (bodd n, div2 n) := rfl

@[simp]
theorem div2_bit0 (n) : div2 (2 * n) = n :=
  div2_bit false n

-- simp can prove this
theorem div2_bit1 (n) : div2 (2 * n + 1) = n :=
  div2_bit true n

/-! ### `bit0` and `bit1` -/

theorem bit_add : ∀ (b : Bool) (n m : ℕ), bit b (n + m) = bit false n + bit b m
  | true,  _, _ => by dsimp [bit]; omega
  | false, _, _ => by dsimp [bit]; omega

theorem bit_add' : ∀ (b : Bool) (n m : ℕ), bit b (n + m) = bit b n + bit false m
  | true,  _, _ => by dsimp [bit]; omega
  | false, _, _ => by dsimp [bit]; omega

theorem bit_ne_zero (b) {n} (h : n ≠ 0) : bit b n ≠ 0 := by
  cases b <;> dsimp [bit] <;> omega

@[simp]
theorem bit_div_two (b n) : bit b n / 2 = n := by
  rw [bit_val, Nat.add_comm, add_mul_div_left, div_eq_of_lt, Nat.zero_add]
  · cases b <;> decide
  · decide

@[simp]
theorem bit_shiftRight_one (b n) : bit b n >>> 1 = n :=
  bit_div_two b n

@[simp]
theorem bitCasesOn_bit {motive : ℕ → Sort u} (h : ∀ b n, motive (bit b n)) (b : Bool) (n : ℕ) :
    bitCasesOn (bit b n) h = h b n := by
  change congrArg motive (bit b n).bit_testBit_zero_shiftRight_one ▸ h _ _ = h b n
  generalize congrArg motive (bit b n).bit_testBit_zero_shiftRight_one = e; revert e
  rw [testBit_bit_zero, bit_shiftRight_one]
  intros; rfl

@[simp]
theorem bitCasesOn_bit0 {motive : ℕ → Sort u} (H : ∀ b n, motive (bit b n)) (n : ℕ) :
    bitCasesOn (2 * n) H = H false n :=
  bitCasesOn_bit H false n

@[simp]
theorem bitCasesOn_bit1 {motive : ℕ → Sort u} (H : ∀ b n, motive (bit b n)) (n : ℕ) :
    bitCasesOn (2 * n + 1) H = H true n :=
  bitCasesOn_bit H true n

theorem bit_cases_on_injective {motive : ℕ → Sort u} :
    Function.Injective fun H : ∀ b n, motive (bit b n) => fun n => bitCasesOn n H := by
  intro H₁ H₂ h
  ext b n
  simpa only [bitCasesOn_bit] using congr_fun h (bit b n)

@[simp]
theorem bit_cases_on_inj {motive : ℕ → Sort u} (H₁ H₂ : ∀ b n, motive (bit b n)) :
    ((fun n => bitCasesOn n H₁) = fun n => bitCasesOn n H₂) ↔ H₁ = H₂ :=
  bit_cases_on_injective.eq_iff

theorem bit_eq_zero_iff {n : ℕ} {b : Bool} : bit b n = 0 ↔ n = 0 ∧ b = false := by
  constructor
  · cases b <;> simp [Nat.bit]; omega
  · rintro ⟨rfl, rfl⟩
    rfl

lemma bit_le : ∀ (b : Bool) {m n : ℕ}, m ≤ n → bit b m ≤ bit b n
  | true, _, _, h => by dsimp [bit]; omega
  | false, _, _, h => by dsimp [bit]; omega

lemma bit_lt_bit (a b) (h : m < n) : bit a m < bit b n := calc
  bit a m < 2 * n   := by cases a <;> dsimp [bit] <;> omega
        _ ≤ bit b n := by cases b <;> dsimp [bit] <;> omega

/--
The same as `binaryRec_eq`,
but that one unfortunately requires `f` to be the identity when appending `false` to `0`.
Here, we allow you to explicitly say that that case is not happening,
i.e. supplying `n = 0 → b = true`. -/
theorem binaryRec_eq' {motive : ℕ → Sort*} {z : motive 0} {f : ∀ b n, motive n → motive (bit b n)}
    (b n) (h : f false 0 z = z ∨ (n = 0 → b = true)) :
    binaryRec z f (bit b n) = f b n (binaryRec z f n) := by
  by_cases h' : bit b n = 0
  case pos =>
    obtain ⟨rfl, rfl⟩ := bit_eq_zero_iff.mp h'
    simp only [imp_false, or_false, eq_self_iff_true, not_true, reduceCtorEq] at h
    unfold binaryRec
    exact h.symm
  case neg =>
    rw [binaryRec, dif_neg h']
    change congrArg motive (bit b n).bit_testBit_zero_shiftRight_one ▸ f _ _ _ = _
    generalize congrArg motive (bit b n).bit_testBit_zero_shiftRight_one = e; revert e
    rw [testBit_bit_zero, bit_shiftRight_one]
    intros; rfl

theorem binaryRec_eq {motive : Nat → Sort u} {z : motive 0}
    {f : ∀ b n, motive n → motive (bit b n)}
    (h : f false 0 z = z) (b n) :
    binaryRec z f (bit b n) = f b n (binaryRec z f n) :=
  binaryRec_eq' b n (.inl h)

/-- The same as `binaryRec`, but the induction step can assume that if `n=0`,
  the bit being appended is `true`-/
@[elab_as_elim, specialize]
def binaryRec' {motive : ℕ → Sort*} (z : motive 0)
    (f : ∀ b n, (n = 0 → b = true) → motive n → motive (bit b n)) :
    ∀ n, motive n :=
  binaryRec z fun b n ih =>
    if h : n = 0 → b = true then f b n h ih
    else
      have : bit b n = 0 := by
        rw [bit_eq_zero_iff]
        cases n <;> cases b <;> simp at h ⊢
      congrArg motive this ▸ z

/-- The same as `binaryRec`, but special casing both 0 and 1 as base cases -/
@[elab_as_elim, specialize]
def binaryRecFromOne {motive : ℕ → Sort*} (z₀ : motive 0) (z₁ : motive 1)
    (f : ∀ b n, n ≠ 0 → motive n → motive (bit b n)) :
    ∀ n, motive n :=
  binaryRec' z₀ fun b n h ih =>
    if h' : n = 0 then
      have : bit b n = bit true 0 := by
        rw [h', h h']
      congrArg motive this ▸ z₁
    else f b n h' ih

@[simp]
theorem zero_bits : bits 0 = [] := by simp [Nat.bits]

@[simp]
theorem bits_append_bit (n : ℕ) (b : Bool) (hn : n = 0 → b = true) :
    (bit b n).bits = b :: n.bits := by
  rw [Nat.bits, Nat.bits, binaryRec_eq']
  simpa

@[simp]
theorem bit0_bits (n : ℕ) (hn : n ≠ 0) : (2 * n).bits = false :: n.bits :=
  bits_append_bit n false fun hn' => absurd hn' hn

@[simp]
theorem bit1_bits (n : ℕ) : (2 * n + 1).bits = true :: n.bits :=
  bits_append_bit n true fun _ => rfl

@[simp]
theorem one_bits : Nat.bits 1 = [true] := by
  convert bit1_bits 0
  simp

-- TODO Find somewhere this can live.
-- example : bits 3423 = [true, true, true, true, true, false, true, false, true, false, true, true]
-- := by norm_num

theorem bodd_eq_bits_head (n : ℕ) : n.bodd = n.bits.headI := by
  induction n using Nat.binaryRec' with
  | z => simp
  | f _ _ h _ => simp [bodd_bit, bits_append_bit _ _ h]

theorem div2_bits_eq_tail (n : ℕ) : n.div2.bits = n.bits.tail := by
  induction n using Nat.binaryRec' with
  | z => simp
  | f _ _ h _ => simp [div2_bit, bits_append_bit _ _ h]

end Nat
