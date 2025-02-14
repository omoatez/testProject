import «TestProject».Basic
import Lean
import Std
import Aesop


open Std
open Lean Meta Tactic TryThis
open Elab
open Tactic
open Command
open Term
open Lean Linter
open Aesop
open PrettyPrinter
open Parser.Tactic

register_option linter.structureProof : Bool := {
  defValue := true
}

syntax (name := showQuestion) "show?" : tactic

@[tactic showQuestion] def evalShowQuestion : Tactic := fun _stx => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let goalTypeString ← PrettyPrinter.delab goalType

  let suggestionText : SuggestionText := "apply some_tactic"
  let suggestion : Suggestion := {
    suggestion := suggestionText,
    preInfo? := some "Try this tactic: ",
    postInfo? := none,
    style? := none,
    messageData? := none,
    toCodeActionTitle? := none
  }
  Lean.Meta.Tactic.TryThis.addSuggestion _stx suggestion
  return ()

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
      -- TryThis.addSuggestion stx suggestion
      --logLint linter.structureProof stx m!"{suggestionText}"
    | _ => logLint linter.structureProof stx "no TermInfo"
  | `(tactic| let $hyp := $proof) => do
      let info? := infoTrees.findSome? (fun infoT => InfoTree.foldInfo (init := none) (fun ctxInfo info oldState => if info.stx == hyp then some (ctxInfo, info) else oldState) infoT)
      match info? with
      | none => logLint linter.structureProof stx "No info found for the following syntax"
      | some (ctxInfo, Info.ofTermInfo termInfo) =>
          let type ← ctxInfo.runMetaM termInfo.lctx (do PrettyPrinter.delab (← instantiateMVars (← inferType termInfo.expr)))
          let suggestionText ← `(tactic| let $hyp : $type := $proof)
          logLint linter.structureProof stx m!"{suggestionText}"
      | _ => logLint linter.structureProof stx "no TermInfo"
  | _ => pure ()

def suggestHaveSyntax(stx : Syntax) (infoTrees : Array InfoTree) : TermElabM Unit := do
  match stx with
  | `(tactic| have $hyp := $proof) => do
    let info? := infoTrees.findSome? (fun infoT =>
      InfoTree.foldInfo (init := none)
        (fun ctxInfo info oldState =>
          if info.stx == hyp then some (ctxInfo, info) else oldState
        ) infoT
    )

    match info? with
    | none =>
      logLint linter.structureProof stx "No info found for the following syntax"
    | some (ctxInfo, Info.ofTermInfo termInfo) =>
      let type ← ctxInfo.runMetaM termInfo.lctx (do
        PrettyPrinter.delab (← instantiateMVars (← inferType termInfo.expr))
      )
      let suggestionText ← `(tactic | have $hyp : $type := $proof)
      TryThis.addSuggestion stx suggestionText
    | _ => logLint linter.structureProof stx "no TermInfo"

  | `(tactic| let $hyp := $proof) => do
    let info? := infoTrees.findSome? (fun infoT =>
      InfoTree.foldInfo (init := none)
        (fun ctxInfo info oldState =>
          if info.stx == hyp then some (ctxInfo, info) else oldState
        ) infoT
    )

    match info? with
    | none =>
      logLint linter.structureProof stx "No info found for the following syntax"
    | some (ctxInfo, Info.ofTermInfo termInfo) =>
      let type ← ctxInfo.runMetaM termInfo.lctx (do
        PrettyPrinter.delab (← instantiateMVars (← inferType termInfo.expr))
      )
      let suggestionText ← `(tactic | let $hyp : $type := $proof)
      TryThis.addSuggestion stx suggestionText
    | _ => logLint linter.structureProof stx "no TermInfo"

  | _ => pure ()

syntax (name := ssuffices) "SSuffices " term " by" tacticSeq : tactic

@[tactic ssuffices] def evalSSuffices : Tactic := fun stx => do
  match stx with
  | `(tactic| SSuffices $expectedType by $tactic) => do
    -- Get the current goal and its type
    evalTactic tactic
    let goals ← getGoals
    if (goals.length > 1) then throwError "more than one goal"
    if goals.length = 0 then throwError "no goal"
    let firstGoal := goals[0]!
    withMainContext do
      let expectedTypeTerm ← Tactic.elabTerm expectedType none
      let goalType ← firstGoal.getType
      let isEqual ← isDefEq goalType expectedTypeTerm
      if (!isEqual) then throwError "different Type"
  | _ => throwUnsupportedSyntax

syntax (name := SSuffices) "SSuffices?" "by" tacticSeq : tactic
@[tactic SSuffices] def evalSSufficesQuestionMark : Tactic := fun stx => do

  match stx with
  |`(tactic| SSuffices? by $tacticSeq) => do
    evalTactic tacticSeq
    let newGoal ← getMainGoal
    let newGoalType ← newGoal.getType
    let newGoalTypeString ← PrettyPrinter.delab newGoalType

    logInfo m!"New goal type: {newGoalTypeString}"

    let suggestionText ←  `(tactic | SSuffices $newGoalTypeString by $tacticSeq)

    TryThis.addSuggestion stx suggestionText
  | _ => throwUnsupportedSyntax


def iterateAndSuggest(code: Syntax): CommandElabM Unit := do
  if !linter.structureProof.get (← getOptions) then
    return
  let cats := (Parser.parserExtension.getState (← getEnv)).categories
  let some tactics := Parser.ParserCategory.kinds <$> cats.find? `tactic
    |return
  let (_, tacticMap)  ← StateRefT'.run (m := IO)  (Batteries.Linter.UnreachableTactic.getTactics ∅ (fun k => tactics.contains k) code) ∅
  let infoTrees := (← get).infoState.trees.toArray
  for (_,tactic) in tacticMap do
    liftTermElabM (suggestSimplifiedHaveSyntax tactic infoTrees)
  pure ()

syntax (name := simp?) "simp?" (config)? (discharger)? (&" only")?
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "]")? (location)?:tactic

@[tactic simp?]
def evalSimpQuestionMark : Tactic := fun stx => do
  evalTactic (← `(tactic| simp))

  let goal ← getMainGoal
  let mainGoalType ← goal.getType

  let mainGoalTypeStx ← delab mainGoalType
  let suggestionText ← `(tactic| SSuffices $mainGoalTypeStx by simp)
  TryThis.addSuggestion stx suggestionText

syntax (name := rw?) "rw?"  (config)? (&" only")?
  (" [" withoutPosition((rwRule),*,?) "]")? (location)?: tactic

@[tactic rw?]
def evalRwQuestionMark : Tactic := fun stx => do
  evalTactic (← `(tactic| rw[]))
  let goal ← getMainGoal
  let mainGoalType ← goal.getType

  let mainGoalTypeStx ← delab mainGoalType

  let suggestionText ← `(tactic| SSuffices $mainGoalTypeStx by rw[])
  TryThis.addSuggestion stx suggestionText


def structureProofLinter : Linter where
  run := iterateAndSuggest
  name := `structureProofLinter

initialize addLinter structureProofLinter
