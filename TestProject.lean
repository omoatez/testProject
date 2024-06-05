import «TestProject».Basic
import Lean
import Std


open Std Linter
open Lean Meta Tactic TryThis
open Elab
open Tactic
open Command
open Term
open Lean Linter

register_option linter.structureProof : Bool := {
  defValue := true
}

def suggestSimplifiedHaveSyntax  (stx : Syntax) : TermElabM Unit := do
  match stx with
  | `(tactic| have $hyp := $proof) => do
    -- Expr in a MetaM context
    let infoTrees := (← getInfoState).trees.toArray
    let info? := infoTrees.findSome? (fun infoT => InfoTree.findInfo? (fun info => info.stx == hyp) infoT)

    match info? with
    | none => logLint linter.structureProof stx "No info found for the following syntax"
    | some (Info.ofTermInfo termInfo) =>
      match termInfo.expectedType? with
      | none => logLint linter.structureProof stx "No expected type"
      | some expectedType =>
        let expectedTypeExpr : Lean.Expr := expectedType
        let typeStx ← PrettyPrinter.delab (← instantiateMVars expectedTypeExpr)
        let suggestionText ←  `(tactic | have $hyp : $typeStx := $proof)
        let suggestion: TryThis.Suggestion := {
          suggestion := suggestionText,
          preInfo? := none,
          postInfo? := none,
          style? := none
        }
        TryThis.addSuggestion stx suggestion
    | _ => logLint linter.structureProof stx "no TermInfo"
  | _ => pure ()



def iterateAndSuggest(code: Syntax): CommandElabM Unit := do
  if !linter.structureProof.get (← getOptions) then
    return
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
