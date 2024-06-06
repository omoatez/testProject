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

def suggestSimplifiedHaveSyntax  (stx : Syntax) (infoTrees : Array InfoTree) : TermElabM Unit := do
  match stx with
  | `(tactic| have $hyp := $proof) => do
    -- Expr in a MetaM context
    logLint linter.structureProof stx m!"{infoTrees.size}"
    let info? := infoTrees.findSome? (fun infoT => InfoTree.foldInfo (init := none) (fun ctxInfo info oldState => if info.stx == hyp then some (ctxInfo,info) else oldState ) infoT)

    match info? with
    | none => logLint linter.structureProof stx "No info found for the following syntax"
    | some (ctxInfo, Info.ofTermInfo termInfo) =>
      let type ← ctxInfo.runMetaM termInfo.lctx (do PrettyPrinter.delab ( ← instantiateMVars ( ← inferType termInfo.expr) ))
      let suggestionText ←  `(tactic | have $hyp : $type := $proof)
      let suggestion: TryThis.Suggestion := {
        suggestion := suggestionText,
        preInfo? := none,
        postInfo? := none,
        style? := none
      }
      -- TryThis.addSuggestion stx suggestion
      logLint linter.structureProof stx m!"{suggestionText}"
    | _ => logLint linter.structureProof stx "no TermInfo"
  | _ => pure ()



def iterateAndSuggest(code: Syntax): CommandElabM Unit := do
  if !linter.structureProof.get (← getOptions) then
    return
  let cats := (Parser.parserExtension.getState (← getEnv)).categories
  let some tactics := Parser.ParserCategory.kinds <$> cats.find? `tactic
    |return
  let (_, tacticMap)  ← StateRefT'.run (m := IO) (UnreachableTactic.getTactics ∅ (fun k => tactics.contains k) code) ∅
  let infoTrees := (← get).infoState.trees.toArray
  for (_,tactic) in tacticMap do
    liftTermElabM (suggestSimplifiedHaveSyntax tactic infoTrees)
  pure ()

def structureProofLinter : Linter where
  run := iterateAndSuggest
  name := `structureProofLinter

initialize addLinter structureProofLinter
