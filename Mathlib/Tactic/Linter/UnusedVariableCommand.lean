/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command

/-!
#  The "unusedVariableCommand" linter

The "unusedVariableCommand" linter emits a warning when a variable declared in `variable ...`
is globally unused.
-/

open Lean Parser Elab Command

namespace Lean.Syntax
/-!
# `Syntax` filters
-/

/--
`filterMapM stx f` takes as input
* `stx : Syntax` and
* a monadic function `f : Syntax → m (Option α)`.

It returns the array of all "`some`" values of `f` on all syntax sub-terms of `stx`.
-/
partial
def filterMapM {α} {m : Type → Type} [Monad m] (stx : Syntax) (f : Syntax → m (Option α)) :
    m (Array α) := do
  let nargs := (← stx.getArgs.mapM (·.filterMapM f)).flatten
  match ← f stx with
    | some new => return nargs.push new
    | none => return nargs

/--
`filterMap stx f` takes as input
* `stx : Syntax` and
* a function `f : Syntax → Option α`.

It returns the array of all "`some`" values of `f` on all syntax sub-terms of `stx`.
-/
def filterMap {α} (stx : Syntax) (f : Syntax → Option α) : Array α :=
  stx.filterMapM (m := Id) f

/--
`filter stx f` takes as input
* `stx : Syntax` and
* a predicate `f : Syntax → Bool`.

It returns the array of all syntax sub-terms of `stx` satisfying `f`.
-/
def filter (stx : Syntax) (f : Syntax → Bool) : Array Syntax :=
  stx.filterMap (fun s => if f s then some s else none)

end Lean.Syntax

namespace Mathlib.Linter

/--
The "unusedVariableCommand" linter emits a warning when a variable declared in `variable ...`
is globally unused.
-/
register_option linter.unusedVariableCommand : Bool := {
  defValue := true
  descr := "enable the unusedVariableCommand linter"
}

namespace UnusedVariableCommand

/--
`usedVarsRef` collects
* the unique names of the variables that have been used somewhere in its `NameSet` factor and
* the mapping from unique names to the `Syntax` node of the corresponding variable in its second
  factor.

There is an exception: for variables introduced with `variable ... in`, the `Syntax`
node is the whole `variable` command.
-/
initialize usedVarsRef : IO.Ref (NameSet × NameMap Syntax) ← IO.mkRef ({}, {})

/-- Add the (unique) name `a` to the `NameSet` of variable names that some declaration used. -/
def usedVarsRef.addUsedVarName (a : Name) : IO Unit := do
  usedVarsRef.modify fun (used, varsDict) => (used.insert a, varsDict)

/-- Add the assignment `a → ref` to the `NameMap Syntax` of unique variable names. -/
def usedVarsRef.addDict (a : Name) (ref : Syntax) : IO Unit := do
  usedVarsRef.modify fun (used, varsDict) =>
    (used, if varsDict.contains a then varsDict else varsDict.insert a ref)

/--
`includedVariables plumb` returns the unique `Name`, the user `Name` and the `Expr` of
each `variable` that is present in the current context.
While doing this, it also updates the "unique-var-name-to-Syntax" dictionary with the variables
from the local context.

Finally, the `Bool`ean `plumb` decides whether or not `includedVariables` also extends the
`NameSet` of variables that have been used in some declaration.
-/
def includedVariables (plumb : Bool) : TermElabM (Array (Name × Name × Expr)) := do
  let c ← read
  let fvs := c.sectionFVars
  let mut varIds := #[]
  let lctx ← getLCtx
  for (a, b) in fvs do
    let ref ← getRef
    if (lctx.findFVar? b).isNone then
      usedVarsRef.addDict a ref
    if (lctx.findFVar? b).isSome then
      let mut fd := .anonymous
      for (x, y) in c.sectionVars do
        if y == a then fd := x
      varIds := varIds.push (a, fd, b)
      if plumb then
        usedVarsRef.addUsedVarName a
  return varIds

/--
The tactic `included_variables` reports which variables are included in the current declaration.

The variant `included_variables plumb` is intended only for the internal use of the
unused variable command linter: besides printing the message, `plumb` also adds records that
the variables included in the current declaration really are included.
-/
elab "included_variables" plumb:(ppSpace &"plumb")? : tactic => do
    let (_plb, usedUserIds) := (← includedVariables plumb.isSome).unzip
    let msgs ← usedUserIds.mapM fun (userName, expr) =>
      return m!"'{userName}' of type '{← Meta.inferType expr}'"
    if ! msgs.isEmpty then
      logInfo m!"{msgs.foldl (m!"{·}\n" ++ m!"* {·}") "Included variables:"}"

/-- The `NameSet` of all the `SyntaxNodeKinds` of all the binders. -/
abbrev binders : NameSet := NameSet.empty
  |>.insert ``Lean.Parser.Term.explicitBinder
  |>.insert ``Lean.Parser.Term.strictImplicitBinder
  |>.insert ``Lean.Parser.Term.implicitBinder
  |>.insert ``Lean.Parser.Term.instBinder

/--
`findBinders stx` extracts all syntax nodes in `stx` representing binders.

*Note*. This is a crude function and more structured solutions, such as `mkThm`
should be preferred, if possible.
-/
partial
def findBinders (stx : Syntax) : Array Syntax :=
  stx.filter (binders.contains ·.getKind)

/--
`getExtendBinders stx` finds the first `extends` node in `stx` and, from there,
extracts all binders, returning them as an array of instance-implicit syntax nodes.
-/
def getExtendBinders {m} [Monad m] [MonadRef m] [MonadQuotation m] (stx : Syntax) :
    m (Array Syntax) := do
  if let some exts := stx.find? (·.isOfKind ``Lean.Parser.Command.extends) then
    let exts := exts[1].getArgs.filter (·.getAtomVal != ",")
    let exts ← exts.mapM (`(Lean.Parser.Term.instBinder| [$(⟨·⟩)]))
    return exts
  else return #[]

variable (nm : Ident) (binders : TSyntaxArray [`ident, ``Term.hole, ``Term.bracketedBinder])
  (typ : Syntax) in
/--
`mkThmCore nm binders typ` returns the `Syntax` for
`theorem nm binders* : type := by included_variables plumb; sorry`.
-/
def mkThmCore {m} [Monad m] [MonadRef m] [MonadQuotation m] : m Syntax :=
  `(command| theorem $nm $binders* : $(⟨typ⟩) := by included_variables plumb; sorry)

/-- `mkThm stx` inspects `stx` and, if it is a declaration, it extracts, where available,
the binders and the expected type, to produce a new `theorem` using `mkThmCore`.

This is the more "structured" sibling of `mkThm'`, that tries to handle the cases that slip through
the cracks of the matching in `mkThm`.
-/
def mkThm {m} [Monad m] [MonadQuotation m] [MonadRef m] (stx : Syntax) : m Syntax := do
  let fls := mkIdent `False
  let (id, hyps, typ) := ← match stx with
    | `($_:declModifiers abbrev $did:declId $as* : $t $_:declVal) =>
      return (did, as, (← `($(mkIdent `toFalse) $t)))
    | `($_:declModifiers def $did:declId $as* : $t $_:declVal) =>
      return (did, as, (← `($(mkIdent `toFalse) $t)))
    | `($_:declModifiers def $did:declId $as* $_:declVal) =>
      return (did, as, fls)
    | `($_:declModifiers instance $(_optNamedPrio)? $(did)? $as* : $t $_:declVal) =>
      return (did.getD default, as, (← `($(mkIdent `toFalse) $t)))
    | `($_:declModifiers theorem $did:declId $as* : $t $_:declVal) =>
      return (did, as, (← `($(mkIdent `toFalse) $t)))
    | `($_:declModifiers structure $did:declId $as* extends $es,* :=
        $(_optCtor)? $_t:structFields) => do
      let exts ← es.getElems.mapM fun d => `(Term.instBinder| [$d])
      return (did, as.map (⟨·⟩) ++ exts.map (⟨·⟩), fls)
    | _ => return (default, #[], fls)
  let newNm := id.raw[0].getId ++ `sfx
  mkThmCore (mkIdent newNm) hyps typ

/-- `getPropValue stx` assumes that `stx` is the syntax of some declaration and returns a
`Prop`-valued `Syntax` term.
It also assumes that there is a function `toFalse : _ → Prop`.
(Such a function is internally generated by the rest of the linter and its value is always `False`.)

If `stx` is a non-`structure` that contains a `typeSpec` node `ts` (e.g. all `theorem`s) , then
`getPropValue` returns `toFalse ts`, otherwise it returns `False`.
-/
def getPropValue {m} [Monad m] [MonadRef m] [MonadQuotation m] (stx : Syntax) : m Syntax := do
  let flse ← `($(mkIdent `False))
  if (stx.find? (·.isOfKind ``Command.structure)).isSome then
    return flse
  if let some ts := stx.find? (·.isOfKind ``Term.typeSpec) then
    `($(mkIdent `toFalse) $(⟨ts[1]⟩))
  else
    return flse

/--
`mkThm' cmd typeSorry` takes as input the `Syntax` `cmd` and an optional `Bool`ean `typeSorry`
with default value `false`.

It returns the syntax for `theorem nm (binders) : type := by included_variables plumb; sorry`
where
* `nm` is a "new" name;
* `(binders)` are the binders that can be found in the syntax of `cmd`, including the ones
  mentioned in an `extends` statement;
* if `cmd` has a type specification `t`, then `type` is `toFalse t`, otherwise it is `False`.

The idea is that `mkThm' cmd` is "as close as possible" to `cmd` in terms of implied variables,
so that `included_variables plumb` will label all variables that `cmd` uses as actually used.

This is the less "structured" sibling of `mkThm`.
-/
def mkThm' (cmd : Syntax) (typeSorry : Bool := false) : CommandElabM Syntax := do
  let exts ← getExtendBinders cmd
  let typ ← if typeSorry then do return (← `($(mkIdent `toFalse) sorry)).raw else getPropValue cmd
  mkThmCore (mkIdent `helr) ((findBinders cmd ++ exts).map (⟨·⟩)) typ

open Lean.Parser.Term in
/--
Like `Lean.Elab.Command.getBracketedBinderIds`, but returns the identifier `Syntax`,
rather than the `Name`, in the given bracketed binder.
-/
def getBracketedBinderIds : Syntax → CommandElabM (Array Syntax)
  | `(bracketedBinderF|($ids* $[: $ty?]? $(_annot?)?)) => return ids
  | `(bracketedBinderF|{$ids* $[: $ty?]?})             => return ids
  | `(bracketedBinderF|⦃$ids* : $_⦄)                   => return ids
  | `(bracketedBinderF|[$id : $_])                     => return #[id]
  | `(bracketedBinderF|[$f])                           => return #[f]
  | _                                                  => throwUnsupportedSyntax

/-- `getForallStrings expr` takes as input an `Expr`ession `expr`, and recursively extracts a
string from `expr`, for every `.forallE` constructor with which `expr` starts.

If the `.forallE` is not an instance, then the string is the name of the binder.
If the `.forallE` is an instance, then the string is the pretty-printed name of the instance,
up to the first space character.

These strings are used to find used variables in the case of `def`-based declarations.
For this reason, we only really return the binder names up to the first space-character.
The heuristic is that if the binder name is a simple variable name, we are ok.
Otherwise, the beginning of the instance is a good approximation to match the instance with a
`variable` introduced instance-binder.

This is not perfect, but works well in practice.
-/
def getForallStrings : Expr → CommandElabM (Array String)
  | .forallE na x bod bi | .lam na x bod bi => do
    if let .instImplicit := bi then
      let x_no_bvars := x.replace (if ·.ctorName == "bvar" then some (.const `Nat []) else none)
      let (str, _) ← liftCoreM do Meta.MetaM.run do return (← Meta.ppExpr (x_no_bvars)).pretty
      return #[((str.splitOn ".{").getD 0 "").takeWhile (· != ' ')] ++ (← getForallStrings bod)
    else
      return #[((na.toString.splitOn ".{").getD 0 "").takeWhile (· != ' ')] ++
              (← getForallStrings bod)
  | _ => return #[]

/--
`getUsedVariableNames pos` takes as input a position `pos`.

Assuming that `pos` is the beginning of a declaration identifiers, `getUsedVariableNames` finds
which declaration starts at `pos`, retrieves its `type` and returns the binder names of `type`.

This is used on `def`-like declaration to try to determine the section `variable`s that the
declaration uses.
-/
def getUsedVariableNames (pos : String.Pos) : CommandElabM (Array String) := do
  let fm ← getFileMap
  let declRangeExt := declRangeExt.getState (← getEnv)
  let names := declRangeExt.toList.find? fun d => (d.2.selectionRange.pos == fm.toPosition pos)
  let decl := ((← getEnv).find? (names.getD default).1).getD default
  getForallStrings decl.type

/-- `lemmaToThm stx` assumes that `stx` is of kind `lemma` and converts it into `theorem`. -/
def lemmaToThm (stx : Syntax) : Syntax :=
  let toDecl := stx.replaceM (m := Id) fun d =>
    match d with
      | .node kind `group args => return some (.node kind `Lean.Parser.Command.theorem args)
      | _ => return none
  let toDecl := toDecl.replaceM (m := Id) fun d =>
    match d with
      | atm@(.atom _ "lemma") => return (mkAtomFrom atm "theorem")
      | _ => return none
  let toDecl := toDecl.replaceM (m := Id) fun d =>
    match d with
      | .node kind `lemma args => return some (.node kind `Lean.Parser.Command.declaration args)
      | _ => return none
  toDecl

@[inherit_doc Mathlib.Linter.linter.unusedVariableCommand]
def unusedVariableCommandLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.unusedVariableCommand (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  -- rather than just reporting on a `Parser.isTerminalCommand`,
  -- we look inside `stx` to find a terminal command.
  -- This simplifies testing: writing `open Nat in #exit` prints the current linter output
  if (stx.find? (Parser.isTerminalCommand ·)).isSome then
      let (used, all) ← usedVarsRef.get
      let sorted := used.toArray.qsort (·.toString < ·.toString)
      let unused := all.toList.filter (!sorted.contains ·.1)
      for (uniq, user) in unused do
        match uniq.eraseMacroScopes with
          | .anonymous => Linter.logLint linter.unusedVariableCommand user m!"'{user}' is unused"
          | x          => Linter.logLint linter.unusedVariableCommand user m!"'{x}' is unused"
  -- if there is a `variable` command in `stx`, then we update `usedVarsRef` with all the
  -- information that is available
  if (stx.find? (·.isOfKind ``Lean.Parser.Command.variable)).isSome then
    let scope ← getScope
    let pairs := scope.varUIds.zip (← scope.varDecls.mapM getBracketedBinderIds).flatten
    usedVarsRef.modify fun (used, varsDict) => Id.run do
      let mut newVarsDict := varsDict
      for (uniq, user) in pairs do
        newVarsDict := newVarsDict.insert uniq user
      (used, newVarsDict)
  -- On all declarations that are not examples, we "rename" them, so that we can elaborate
  -- their syntax again, and we replace `:= proof-term` by `:= by included_variables plumb: sorry`
  -- in order to update the `usedVarsRef` counter.
  -- TODO: find a way to deal with proofs that use the equation compiler directly.
  if let some decl := stx.find? (#[``declaration, `lemma].contains <|·.getKind) then
    let usedVarNames := ← do
      if #[``definition, ``Command.structure, ``Command.abbrev].contains decl[1].getKind then
        let declIdStx := (decl.find? (·.isOfKind ``declId)).getD default
        getUsedVariableNames (declIdStx.getPos?.getD default)
      else return #[]
    -- Skip examples, since they have access to all the variables
    if decl[1].isOfKind ``Lean.Parser.Command.example then
      return
    let toFalse := mkIdent `toFalse
    let toThm : Syntax := if decl.isOfKind `lemma then lemmaToThm decl else decl
    let renStx ← mkThm toThm
    -- Replace the declaration in the initial `stx` with the "revised" one.
    -- This handles `include h in` and other "`in`"s.
    let newRStx : Syntax := stx.replaceM (m := Id)
      (if · == decl then return some renStx else return none)
    let s ← get
    elabCommand (← `(def $toFalse (S : Sort _) := False))
    try
      elabCommand newRStx
    catch _ =>
      elabCommand (← mkThm' decl true)
    set s
    let left2 := (← usedVarsRef.get).2.toList
    let left := left2.map Prod.fst
    let _leftPretty := (left2.map Prod.snd).map fun l => l.prettyPrint.pretty
    let mut filt := []
    let mut filt2 := []
    for s in usedVarNames do
      filt2 := filt2 ++ left2.filter fun (_a, b) =>
        let comp := if _a.eraseMacroScopes.isAnonymous then b.prettyPrint.pretty else _a.toString
        (s.isPrefixOf comp)

      filt := filt ++ left.filter (s.isPrefixOf ·.toString)
    for (s, _) in filt2 do
      usedVarsRef.addUsedVarName s

initialize addLinter unusedVariableCommandLinter

end UnusedVariableCommand

end Mathlib.Linter