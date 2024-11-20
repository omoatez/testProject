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
      logLint linter.structureProof stx m!"{suggestionText}"
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

 -- TODO refactor simp??
syntax (name := simp??) "ssimp" : tactic

@[tactic simp??] def evalSimpQuestion : Tactic := fun stx => do
  -- Get the current goal and its type
  let goal ← getMainGoal
  let goalType ← goal.getType

  -- Apply the simpGoal function
  let (simplifiedResult, stats) ← simpGoal goal {}

  match simplifiedResult with
  | none =>
    logInfo "simp made no progress"
  | some (_, newMVarId) =>
    if stats.usedTheorems.size == 0 then
      logInfo "simp made no progress"
    else
      let U ← mkFreshExprMVar (← Lean.MVarId.getType newMVarId)
      let suggestionText ← `(tactic | suffices $(mkIdent `hyp):ident : _ by simp)
      Lean.Meta.Tactic.TryThis.addSuggestion stx suggestionText
      let subgoal1 ← mkFreshExprMVar (← Lean.MVarId.getType newMVarId)
      replaceMainGoal [newMVarId, subgoal1.mvarId!]

      setGoals [newMVarId]
      evalTactic (← `(tactic| simp))
      pure ()



syntax (name := simpSeq??) "simpSeq??" tacticSeq : tactic

@[tactic simpSeq??] def evalSimpSeqQuestion : Tactic := fun stx => do
  match stx with
  | `(tactic| simpSeq?? $tacticSeq) => do
    let mut suggestions := #[]
    let mut newGoals := #[]

    let tacticList := tactics

    for tactic in tacticList do
      setGoals [← getMainGoal]

      evalTactic tactic

      let goal ← getMainGoal
      let goalType ← goal.getType

      let (simplifiedResult, stats) ← simpGoal goal {}
      match simplifiedResult with
      | none =>
        logInfo m!"simp made no progress after: {tactic}"
      | some (_, newMVarId) =>
        if stats.usedTheorems.size == 0 then
          logInfo m!"simp made no progress after: {tactic}"
        else
          let suggestionText ← `(tactic | suffices $(mkIdent `hyp):ident : _ by simp)
          suggestions := suggestions.push suggestionText
          newGoals := newGoals.push newMVarId

    if suggestions.size > 0 then
      let combinedSuggestion ← `(tactic| simpSeq?? $suggestions)
      logInfo m!"Generated combined suggestion: {combinedSuggestion}"
      Lean.Meta.Tactic.TryThis.addSuggestion stx combinedSuggestion
    else
      logInfo "no simplifications were suggested for the sequence."

    replaceMainGoal newGoals.toList
  | _ => throwUnsupportedSyntax


def structureProofLinter : Linter where
  run := iterateAndSuggest
  name := `structureProofLinter

initialize addLinter structureProofLinter
