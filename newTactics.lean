

def structuredCore (tacSeq : TSyntax ``tacticSeq) : TacticM Unit := do
  match (← getUnsolvedGoals) with
  | [] =>
    logWarning m!"No goals to solve, shouldn't reach this, since we can't execute your tactic anyways"
  | [goal] =>
    let tacs ← getTacs tacSeq
    let goalType := (← goal.getDecl).type
    match tacs with
    | #[] => logWarning "No tactics in tacSeq"
    | #[tac] =>
      match tac with
      -- Native Lean 4 tactics
      | `(tactic|suffices $_)
      | `(tactic|show $_)
      | `(tactic|clear $_)
      | `(tactic|have $_:ident : $_:term := $_)
      | `(tactic|let $_:ident : $_:term := $_)
      -- Custom tactics
        =>
        addTrace `structured m!"This tactic is already structured"
        evalTactic tacSeq

      | `(tactic|have $_:hole : $type:term := $rhs) -- hole-named typed
        =>
          let autoName ← mkNameFromTerm type
          let suggestion ← `(tactic|have $autoName : $type := $rhs)
          addTrace `structured m!"Try this: {suggestion}"
          evalTactic tac
      | `(tactic|have : $type:term := $rhs) -- unnamed typed
        =>
          let autoName := mkIdent (.str .anonymous "this")
          let suggestion ← `(tactic|have $autoName : $type := $rhs)
          addTrace `structured m!"Try this: {suggestion}"
          evalTactic tac
      | `(tactic|have $id:ident := $rhs) -- named untyped
        =>
          let autoType ← mkTypeFromTac tac
          let suggestion ← `(tactic|have $id : $autoType := $rhs)
          addTrace `structured m!"Try this: {suggestion}"
          evalTactic tac
      | `(tactic|have $_:hole := $rhs) -- hole-named untyped
        =>
          let autoType ← mkTypeFromTac tac
          let autoName ← mkNameFromTerm autoType
          let suggestion ← `(tactic|have $autoName : $autoType := $rhs)
          addTrace `structured m!"Try this: {suggestion}"
          evalTactic tac
      | `(tactic|have := $rhs) -- unnamed untyped
        =>
          let autoType ← mkTypeFromTac tac
          let autoName := mkIdent (.str .anonymous "this")
          let suggestion ← `(tactic|have $autoName : $autoType := $rhs)
          addTrace `structured m!"Try this: {suggestion}"
          evalTactic tac

      | `(tactic|let $_:hole : $type:term := $rhs)  -- hole-named typed
        =>
          let autoName ← mkNameFromTerm type
          let suggestion ← `(tactic|let $autoName : $type := $rhs)
          addTrace `structured m!"Try this: {suggestion}"
          evalTactic tac
      | `(tactic|let $_:hole := $rhs) -- hole-named untyped
        =>
          let autoType ← mkTypeFromTac tac
          let autoName ← mkNameFromTerm autoType
          let suggestion ← `(tactic|let $autoName : $autoType := $rhs)
          addTrace `structured m!"Try this: {suggestion}"
          evalTactic tac

      | `(tactic|intro $ts:term*)
        =>
          evalTactic tac
          withMainContext do
            -- If intro is called anonymously, manually add the hole for easier function
            if ts.size == 0 then do
              let hole ← `( _ )
              structuredIntros goalType #[hole]
            else
              structuredIntros goalType ts

      | `(tactic|intros $ids*)
        =>
          evalTactic tac
          withMainContext do
            if ids.size == 0 then do
              -- The procedure to handle unbounded intros is to execute tactic
              -- And compare goals, the amount of newFVars is the bound for structuredIntros
              -- That amount of underscores are provided as terms to structuredIntros
              let newGoal ← getMainGoal
              let s ← goalsToStateDiff goal newGoal
              let termHoles := mkArray s.diffFvars.size (← `( _ ))
              structuredIntros goalType termHoles
            else
              let termIds ← ids.mapM mapBinderIdentToTerm
              structuredIntros goalType termIds

      | `(tactic|cases $target:term)
        =>
          structuredCasesOrInduction goal target false
          evalTactic tac
      | `(tactic|induction $target:term)
        =>
          structuredCasesOrInduction goal target true
          evalTactic tac
      | _ => structuredDefault tacSeq goal
    | _ => structuredDefault tacSeq goal
  | _ =>
    addTrace `structured m!"Multiple goals pre-execution is not supported for this tactic.
      Executing tacitc, but no suggestions provided"
    evalTactic tacSeq

-- Elaborate tactic
elab &"structured " t:tacticSeq : tactic =>
  structuredCore t
