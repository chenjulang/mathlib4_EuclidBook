/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Damiano Testa
-/

import Lean.Elab.Command
import Lean.Linter.Util

/-!
# Linter for `attribute [...] in` declarations

Linter for global attributes created via `attribute [...] in` declarations.

The syntax `attribute [instance] instName in` can be used to accidentally create a global instance.
This is **not** obvious from reading the code, and in fact happened twice during the port,
hence, we lint against it.

*Example*: before this was discovered, `Mathlib/Topology/Category/TopCat/Basic.lean`
contained the following code:
```
attribute [instance] ConcreteCategory.instFunLike in
instance (X Y : TopCat.{u}) : CoeFun (X ⟶ Y) fun _ => X → Y where
  coe f := f
```
Despite the `in`, this makes `ConcreteCategory.instFunLike` a global instance.

This seems to apply to all attributes. For example:
```lean
theorem what : False := sorry

attribute [simp] what in
#guard true

-- the `simp` attribute persists
example : False := by simp  -- `simp` finds `what`

theorem who {x y : Nat} : x = y := sorry

attribute [ext] who in
#guard true

-- the `ext` attribute persists
example {x y : Nat} : x = y := by ext
```
Therefore, we lint against this pattern on all instances.

For *removing* attributes, the `in` works as expected.
```lean
/--
error: failed to synthesize
  Add Nat
-/
#guard_msgs in
attribute [-instance] instAddNat in
#synth Add Nat

-- the `instance` persists
/-- info: instAddNat -/
#guard_msgs in
#synth Add Nat

@[simp]
theorem what : False := sorry

/-- error: simp made no progress -/
#guard_msgs in
attribute [-simp] what in
example : False := by simp

-- the `simp` attribute persists
#guard_msgs in
example : False := by simp
```
-/

open Lean Elab Command

namespace Mathlib.Linter

/-- Lint on any occurrence of `attribute [...] name in` which is not `local` or `scoped`:
these are a footgun, as the attribute is applied *globally* (despite the `in`). -/
register_option linter.globalAttributeIn : Bool := {
  defValue := true
  descr := "enable the globalAttributeIn linter"
}

namespace globalAttributeInLinter

/-- Gets the value of the `linter.globalAttributeIn` option. -/
def getLinterGlobalAttributeIn (o : Options) : Bool :=
  Linter.getLinterValue linter.globalAttributeIn o

/--
`getGlobalAttributesIn? cmd` assumes that `cmd` represents a `attribute [...] id in ...` command.
If this is the case, then it returns `(id, #[non-local nor scoped attributes])`.
Otherwise, it returns `default`.
-/
def getGlobalAttributesIn? : Syntax → Option (Ident × Array (TSyntax `attr))
  | `(attribute [$x,*] $id in $_) =>
    let xs := x.getElems.filterMap fun a => match a.raw with
      | `(Parser.Command.eraseAttr| -$_) => none
      | `(Parser.Term.attrInstance| local $_attr:attr) => none
      | `(Parser.Term.attrInstance| scoped $_attr:attr) => none
      | `(attr| $a) => some a
    (id, xs)
  | _ => default

/-- The `globalAttributeInLinter` linter flags any global attributes generated by an
`attribute [...] in` declaration. (This includes the `instance`, `simp` and `ext` attributes.)

Despite the `in`, these define *global* instances, which can be rather misleading.
Instead, remove the `in` or mark them with `local`.
-/
def globalAttributeIn : Linter where run := withSetOptionIn fun stx => do
  unless getLinterGlobalAttributeIn (← getOptions) do
    return
  if (← MonadState.get).messages.hasErrors then
    return
  for s in stx.topDown do
    if let .some (id, nonScopedNorLocal) := getGlobalAttributesIn? s then
      for attr in nonScopedNorLocal do
        Linter.logLint linter.globalAttributeIn attr m!
          "Despite the `in`, the attribute '{attr}' is added globally to '{id}'\n\
          please remove the `in` or make this a `local {attr}`"

initialize addLinter globalAttributeIn

end globalAttributeInLinter

end Mathlib.Linter
