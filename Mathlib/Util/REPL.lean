/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean
import Mathlib.Tactic.GPT.Sagredo.Frontend

open Lean Elab

/-!
# A REPL for Lean.

Communicates via JSON on stdin and stdout. Commands should be separated by blank lines.

Commands may be of the form
```
{ "body" : "import Mathlib.Data.List.Basic\ndef f := 2" }
```
or
```
{ "body" : "example : f = 2 := rfl", "env" : 3 }
```

The `env` field, if present,
must contain a number received in the `env` field of a previous response,
and causes the command to be run in the existing environment.

If there is no `env` field, a new environment is created.

You can only use `import` commands when you do not specify the `env` field.

You can backtrack simply by using earlier values for `env`.

The results are of the form
```
{"sorries":
 [{"pos": {"line": 1, "column": 18},
   "endPos": {"line": 1, "column": 23},
   "goal": "\n⊢ Nat"}],
 "messages":
 [{"severity": "error",
   "pos": {"line": 1, "column": 23},
   "endPos": {"line": 1, "column": 26},
   "data":
   "type mismatch\n  rfl\nhas type\n  f = f : Prop\nbut is expected to have type\n  f = 2 : Prop"}],
 "env": 6}
 ```
 showing any messages generated, or sorries with their goal states.
 Information is generated for tactic mode sorries, but not for term mode sorries.
-/

namespace REPL

section Json

/-- Run Lean commands.
If `env = none`, starts a new session (in which you can use `import`).
If `env = some n`, builds on the existing environment `n`.
-/
structure Run where
  env : Option Nat
  body : String
deriving ToJson, FromJson

/-- Line and column information for error messages and sorries. -/
structure Pos where
  line : Nat
  column : Nat
deriving ToJson, FromJson

/-- Severity of a message. -/
inductive Severity
  | info | warning | error
deriving ToJson, FromJson

/-- A Lean message. -/
structure Message where
  pos : Pos
  endPos : Option Pos
  severity : Severity
  data : String
deriving ToJson, FromJson

/-- Construct the JSON representation of a Lean message. -/
def Message.of (m : Lean.Message) : IO Message := do pure <|
{ pos := ⟨m.pos.line, m.pos.column⟩,
  endPos := m.endPos.map fun p => ⟨p.line, p.column⟩,
  severity := match m.severity with
  | .information => .info
  | .warning => .warning
  | .error => .error,
  data := (← m.data.toString) }

/-- A Lean `sorry`. -/
structure Sorry where
  pos : Pos
  endPos : Pos
  goal : String
deriving ToJson, FromJson

/-- Construct the JSON representation of a Lean sorry. -/
def Sorry.of (ctx : ContextInfo) (g : MVarId) (pos endPos : Lean.Position) :
    IO Sorry := do pure <|
{ pos := ⟨pos.line, pos.column⟩,
  endPos := ⟨endPos.line, endPos.column⟩,
  goal := s!"{(← ctx.ppGoals [g])}" }

/--
A response to a Lean command.
`env` can be used in later calls, to build on the stored environment.
-/
structure Response where
  env : Nat
  messages : List Message
  sorries : List Sorry
deriving ToJson, FromJson

/-- Json wrapper for an error. -/
structure Error where
  message : String
deriving ToJson, FromJson

end Json

open Mathlib.Tactic.GPT.Sagredo

/-- The monadic state for the Lean REPL. -/
structure State where
  environments : Array Environment
  lines : Array Nat

/-- The Lean REPL monad. -/
abbrev M (m : Type → Type) := StateT State m

variable [Monad m] [MonadLiftT IO m]

/-- Get the next available id for a new environment. -/
def nextId : M m Nat := do pure (← get).environments.size

/-- Run a command, returning the id of the new environment, and any messages and sorries. -/
def run (s : Run) : M m Response := do
  let env? := s.env.bind ((← get).environments[·]?)
  let (env, messages, trees) ← processInput s.body env? {} ""
  let messages ← messages.mapM fun m => Message.of m
  let sorries ← trees.bind InfoTree.sorries |>.mapM
    fun ⟨ctx, g, pos, endPos⟩ => Sorry.of ctx g pos endPos
  let lines := s.body.splitOn "\n" |>.length
  let id ← nextId
  modify fun s => { environments := s.environments.push env, lines := s.lines.push lines }
  pure ⟨id, messages, sorries⟩

end REPL

open REPL

/-- Get lines from stdin until a blank line is entered. -/
unsafe def getLines : IO String := do
  match (← (← IO.getStdin).getLine) with
  | "\n" => pure "\n"
  | line => pure <| line ++ (← getLines)

/-- Read-eval-print loop for Lean. -/
unsafe def repl : IO Unit :=
  StateT.run' loop ⟨#[], #[]⟩
where loop : M IO Unit := do
  let query ← getLines
  let json := Json.parse query
  match json with
  | .error e => IO.println <| toString <| toJson (⟨e⟩ : Error)
  | .ok j => match fromJson? j with
    | .error e => IO.println <| toString <| toJson (⟨e⟩ : Error)
    | .ok (r : Run) => IO.println <| toString <| toJson (← run r)
  loop

/-- Main executable function, run as `lake env lean --run Mathlib/Util/REPL.lean`. -/
unsafe def main (_ : List String) : IO Unit := do
  repl
