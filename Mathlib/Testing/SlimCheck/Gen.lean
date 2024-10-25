/-
Copyright (c) 2021 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/
import Mathlib.Control.Random
import Batteries.Data.List.Perm

/-!
# `Gen` Monad

This monad is used to formulate randomized computations with a parameter
to specify the desired size of the result.
This is a port of the Haskell QuickCheck library.

## Main definitions

* `Gen` monad

## Tags

random testing

## References

* https://hackage.haskell.org/package/QuickCheck
-/

universe u v

namespace SlimCheck

open Random

/-- Monad to generate random examples to test properties with.
It has a `Nat` parameter so that the caller can decide on the
size of the examples. -/
abbrev Gen (α : Type u) := ReaderT (ULift Nat) Rand α

namespace Gen

/-- Lift `Random.random` to the `Gen` monad. -/
def chooseAny (α : Type u) [Random Id α] : Gen α :=
  fun _ ↦ rand α

/-- Lift `BoundedRandom.randomR` to the `Gen` monad. -/
def choose (α : Type u) [Preorder α] [BoundedRandom Id α] (lo hi : α) (h : lo ≤ hi) :
    Gen {a // lo ≤ a ∧ a ≤ hi} :=
  fun _ ↦ randBound α lo hi h

lemma chooseNatLt_aux {lo hi : Nat} (a : Nat) (h : Nat.succ lo ≤ a ∧ a ≤ hi) :
    lo ≤ Nat.pred a ∧ Nat.pred a < hi :=
  And.intro (Nat.le_sub_one_of_lt (Nat.lt_of_succ_le h.left)) <|
    show a.pred.succ ≤ hi by
      rw [Nat.succ_pred_eq_of_pos]
      · exact h.right
      · exact lt_of_le_of_lt (Nat.zero_le lo) h.left

/-- Generate a `Nat` example between `x` and `y` (exclusively). -/
def chooseNatLt (lo hi : Nat) (h : lo < hi) : Gen {a // lo ≤ a ∧ a < hi} :=
  Subtype.map Nat.pred chooseNatLt_aux <$> choose Nat (lo.succ) hi (Nat.succ_le_of_lt h)

/-- Get access to the size parameter of the `Gen` monad. -/
def getSize : Gen Nat :=
  return (← read).down

/-- Apply a function to the size parameter. -/
def resize {α : Type*} (f : Nat → Nat) (x : Gen α) : Gen α :=
  withReader (ULift.up ∘ f ∘ ULift.down) x

variable {α : Type u}

/-- Create an `Array` of examples using `x`. The size is controlled
by the size parameter of `Gen`. -/
def arrayOf (x : Gen α) : Gen (Array α) := do
  let (⟨sz⟩ : ULift ℕ) ← ULiftable.up do choose Nat 0 (← getSize) (Nat.zero_le _)
  let mut res := #[]
  for _ in [0:sz] do
    res := res.push (← x)
  pure res

/-- Create a `List` of examples using `x`. The size is controlled
by the size parameter of `Gen`. -/
def listOf (x : Gen α) : Gen (List α) :=
  arrayOf x >>= pure ∘ Array.toList

/-- Given a list of example generators, choose one to create an example. -/
def oneOf (xs : Array (Gen α)) (pos : 0 < xs.size := by decide) : Gen α := do
  let ⟨x, _, h2⟩ ← ULiftable.up <| chooseNatLt 0 xs.size pos
  xs.get ⟨x, h2⟩

/-- Given a list of examples, choose one to create an example. -/
def elements (xs : List α) (pos : 0 < xs.length) : Gen α := do
  let ⟨x, _, h2⟩ ← ULiftable.up <| chooseNatLt 0 xs.length pos
  pure <| xs[x]

open List in
/-- Generate a random permutation of a given list. -/
def permutationOf : (xs : List α) → Gen { ys // xs ~ ys }
  | [] => pure ⟨[], Perm.nil⟩
  | x::xs => do
    let ⟨ys, h1⟩ ← permutationOf xs
    let ⟨n, _, h3⟩ ← ULiftable.up <| choose Nat 0 ys.length (Nat.zero_le _)
    pure ⟨insertNth n x ys, Perm.trans (Perm.cons _ h1) (perm_insertNth _ _ h3).symm⟩

/-- Given two generators produces a tuple consisting out of the result of both -/
def prodOf {α : Type u} {β : Type v} (x : Gen α) (y : Gen β) : Gen (α × β) := do
  let ⟨a⟩ ← ULiftable.up.{max u v} x
  let ⟨b⟩ ← ULiftable.up.{max u v} y
  pure (a, b)

/-- Given two generators randomly choose one to produce a `Sum` -/
def sumOf {α : Type u} {β : Type v} (x : Gen α) (y : Gen β) : Gen (α ⊕ β) :=
  oneOf #[(do let ⟨a⟩ ← ULiftable.up.{max u v} x; return .inl a),
    (do let ⟨b⟩ ← ULiftable.up.{max u v} y; return .inr b)] (pos := by simp)

end Gen

/-- Execute a `Gen` inside the `IO` monad using `size` as the example size -/
def Gen.run {α : Type} (x : Gen α) (size : Nat) : BaseIO α :=
  letI : MonadLift Id BaseIO := ⟨fun f => pure <| Id.run f⟩
  IO.runRand (ReaderT.run x ⟨size⟩:)

end SlimCheck
