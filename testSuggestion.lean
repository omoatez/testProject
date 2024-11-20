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

set_option linter.structureProof true

example : Nat := by
  have h := 1 + 1
  trivial

example (a b : Nat) (h : a = b) : a + 1 = b + 2 := by
  SSuffices False by
    rw [h]
    simp

example (x y : Nat) (h : x + y = y + x) : x + y + 0 = y + x := by
  simpSeq??
    rw [Nat.add_assoc],
    apply Eq.symm,
    simp,
    exact h
  


example (a b c : Nat) : a * (b + c) + b * c = b * c + a * c + a * b := by
  ssimp by
    simp [Nat.mul_add, Nat.add_comm, Nat.add_assoc, Nat.mul_comm]
