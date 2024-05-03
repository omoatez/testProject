import «TestProject»
import Lean
import Lean.Meta
import Lean.Meta.Tactic.TryThis
import Std.Linter
import Std.Tactic.Basic
import Std.Linter.UnreachableTactic


open Std Linter
open Lean Meta Tactic TryThis


def suggestSimplifiedHaveSyntax (ref : Syntax) (stx : Syntax) : MetaM Unit := do
  -- if the syntax is a 'have' tactic
  match stx with
  | `(tactic| have $hyp : $type := $proof) => do
    let replacementText : String := s!""
    let suggestion : TryThis.Suggestion := {
      suggestion := replacementText,
      preInfo? := none,
      postInfo? := none,
      style? := none
    }
    TryThis.addSuggestion ref suggestion
  | _ => pure ()

-- Function to analyze `have` block and display variable types
def analyzeHaveBlock (haveSyntax : Syntax) : MetaM Unit := do
  -- Pattern match on the syntax of the `have` block
  match haveSyntax with
  | `(tactic| have $hyp : $type := $proof) => do
    IO.println s!": {hyp}"
    IO.println s!": {type}"

  | `(tactic| have ($hps : $types) := $proof) => do

    for (hp, tp) in hps.zip types do
      IO.println s!"{hp}, Type: {tp}"
  | _ =>
    pure ()

def iterateAndAnalyzeHave (code : Syntax) : TacticM Unit := do
  for node in code.children do
    if node.getKind == `Lean.Parser.Tactic.have then
      analyzeHaveBlock node

-- Adjust the function's context to match `Elab.Command.CommandElabM`
def iterateAndSuggest(code: Syntax): Elab.Command.CommandElabM Unit := do
  let linterResults ← Std.Linter.UnreachableTactic.unreachableTacticLinter.run code
  match linterResults with
  | some results => do
      for result in results do
        IO.println s!"Lint result: {result}"
  | none =>
      IO.println "No lint results"

  -- Ensure the function ends with `Unit`
  pure ()
