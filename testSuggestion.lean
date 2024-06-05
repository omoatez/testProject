import TestProject
import Lean
set_option linter.structureProof true
theorem example_theorem (a b : Nat) : a + b = b + a := by
  have h₁ := Nat.add_comm a b
  exact h₁

open Lean.Meta

#eval show MetaM Unit from do
  let linters ← Lean.Elab.Command.lintersRef.get
  linters.forM fun linter =>
    IO.println linter.name
