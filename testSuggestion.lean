import Lean
import «TestProject»
set_option linter.structureProof true
theorem example_theorem (a b : Nat) : a + b = b + a := by
  have h₁ := Nat.add_comm a b
  exact h₁

open Lean.Meta

#eval show MetaM Unit from do
  let linters ← Lean.Elab.Command.lintersRef.get
  linters.forM fun linter =>
    IO.println linter.name

example : 2 + 2 = 4 := by
  let x := 2 + 2
  show x = 4
  rfl

example (n : Nat) : n + 0 = n := by
  SSuffices n = n by simp

example (n m : Nat) (h : n + m = m + n) : (n + 0) + m = m + (n + 0) := by
  SSuffices n + m = m + n by simp

example (a b : Nat) : a + b = b + a := by
  apply some_tactic
  rw [Nat.add_comm]

example : T := by
  simp??
