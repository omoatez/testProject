import «TestProject»
import Lean
import Std


open Std Linter
open Lean Meta Tactic TryThis
open Elab
open Tactic
open Command
open Term



def suggestSimplifiedHaveSyntax  (stx : Syntax) : TermElabM Unit := do
  match stx with
  | `(tactic| have $hyp := $proof) => do
    -- Expr in a MetaM context
    let proofExpr ←  elabTerm proof none
    let proofType ← inferType proofExpr
    let typeStx ← PrettyPrinter.delab proofType

    let suggestionText ←  `(tactic | have $hyp : $typeStx := $proof)
    let suggestion: TryThis.Suggestion := {
      suggestion := suggestionText,
      preInfo? := none,
      postInfo? := none,
      style? := none
    }
    TryThis.addSuggestion stx suggestion
  | _ => pure ()

register_option linter.structureProof : Bool := {
  defValue := true
}


def iterateAndSuggest(code: Syntax): CommandElabM Unit := do
  Linter.logLint linter.structureProof code "hello"
  let cats := (Parser.parserExtension.getState (← getEnv)).categories
  let some tactics := Parser.ParserCategory.kinds <$> cats.find? `tactic
    |return
  let (_, tacticMap)  ← StateRefT'.run (m := IO) (UnreachableTactic.getTactics ∅ (fun k => tactics.contains k) code) ∅

  for (_,tactic) in tacticMap do
    liftTermElabM (suggestSimplifiedHaveSyntax tactic)
  pure ()

def structureProofLinter : Linter where
  run := iterateAndSuggest
  name := `structureProofLinter

initialize addLinter structureProofLinter
