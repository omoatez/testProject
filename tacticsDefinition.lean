import Lean
import Lean.Meta
import Lean.Elab.Tactic
import Lean.PrettyPrinter.Delaborator
import Lean.Linter
open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Tactic
open Std Linter
open Lean Linter

-- Define the show? syntax
syntax (name := showQuestion) "show?" : tactic

-- Implement the show? tactic
@[tactic showQuestion] def evalShowQuestion : Tactic := fun stx => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let goalTypeString ← PrettyPrinter.delab goalType
  logInfo m!"Current goal: {goalTypeString}"

-- Define a function to suggest the current goal for the show? tactic
def suggestCurrentGoal (stx : Syntax) (infoTrees : Array InfoTree) : TacticM Unit := do
  match stx with
  | `(tactic| show?) => do
      let goal ← getMainGoal
      let goalType ← goal.getType
      let goalTypeString ← PrettyPrinter.delab goalType
      logInfo m!"Current goal: {goalTypeString} for syntax {stx}"
  | _ => pure ()

-- Define a function to iterate over the syntax tree and suggest the current goal for show?
def iterateAndSuggestShowQuestion (code: Syntax): CommandElabM Unit := do
  if !linter.structureProof.get (← getOptions) then
    return
  let cats := (Parser.parserExtension.getState (← getEnv)).categories
  let some tactics := Parser.ParserCategory.kinds <$> cats.find? `tactic
    | return
  let (_, tacticMap) ← StateRefT'.run (m := IO) (UnreachableTactic.getTactics ∅ (fun k => tactics.contains k) code) ∅
  let infoTrees := (← get).infoState.trees.toArray
  for (_, tactic) in tacticMap do
    liftTermElabM (liftTacticM (suggestCurrentGoal tactic infoTrees))
  pure ()

-- Define the linter for the show? tactic
def structureProofShowQuestionLinter : Linter where
  run := iterateAndSuggestShowQuestion
  name := `structureProofShowQuestionLinter

-- Register the linter
initialize addLinter structureProofShowQuestionLinter
