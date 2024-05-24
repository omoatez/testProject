import Main
import Lean

theorem example_theorem (a b : Nat) : a + b = b + a := by
  have h₁ := by
    exact Nat.add_comm a b
  exact h₁


open Lean.Meta

#eval show MetaM Unit from do
  let linters ← Lean.Elab.Command.lintersRef.get
  linters.forM fun linter =>
    IO.println linter.name
