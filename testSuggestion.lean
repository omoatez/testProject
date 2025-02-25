import Lean
import «TestProject»
import Mathlib
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
  apply some_tactic x = 4
  rfl




set_option linter.structureProof true


 -- theorem odd_square_odd (n : Nat) (h : ∃ k, n = 2 * k + 1) : ∃ m, n^2 = 2 * m + 1 :=
   -- begin
   --   SSuffices? by
  --    obtain ⟨k,h⟩ := h
  --    rw [h]




theorem contrapositive (a b : Prop) :
  (a → b) → (¬b → ¬a) := by
   SSuffices False by intro h1 h2 h3
   show?
   SSuffices b by apply h2
   SSuffices a by apply h1

   apply h3



example (P Q : Prop) : ¬ (P ∨ Q) → (¬ P ∧ ¬ Q) :=by
  SSuffices ¬P ∧ ¬Q by intro h1
  apply And.intro
  intro h2
  apply h1
  left
  SSuffices ¬Q by exact h2
  SSuffices False by intro h3
  SSuffices P ∨ Q by apply h1
  SSuffices Q by right
  exact h3

example (x y : Nat) (h : x = y) : x + 0 = y := by
  simp?  -- Simplifies `x + 0` to `x`
  rw [h]  -- Applies the hypothesis `h : x = y`

example (P Q : Prop) : (P ∧ True) → P := by
  intro p
  simp at p
  exact p


   -- Use the assumption directly

example (P Q : Prop) : (P ∧ True) → P := by
  SSuffices P by intro p  -- Introduce assumptions
  simp at h
  exact p    -- Simplifies `P ∧ True` to `P`


example (P Q : Prop) : (P ∧ Q) → (Q ∧ P) := by
  intro h
  have swapped := And.intro h.right h.left  -- Your tactic should suggest the type here
  exact swapped

example (P Q : Prop) : (P ∧ True) → Q → (P ∧ Q) := by
  intro h1 h2       -- Assume h1 : P ∧ True, h2 : Q
  have  by
    simp at p      -- Simplify h1 to just P      -- Now we have hp : P
  exact ⟨hp, h2⟩

theorem iff_trans (P Q R : Prop) :
  (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
by
  intro hPQ hQR,
  apply Iff.intro,
  { -- Forward direction: P → R
    intro hP,
    apply hQR.mp,  -- Use Q ↔ R to get Q → R
    apply hPQ.mp,  -- Use P ↔ Q to get P → Q
    exact hP },
  { -- Backward direction: R → P
    intro hR,
    apply hPQ.mpr, -- Use P ↔ Q to get Q → P
    apply hQR.mpr, -- Use Q ↔ R to get R → Q
    exact hR }

theorem distrib_imp_and (P Q R : Prop) :
  (P → (Q ∧ R)) → ((P → Q) ∧ (P → R)) :=
by
  intro h
  apply And.intro
  intro hp
  SSuffices P → R by exact (h hp).left
  intro hp
  exact (h hp).right

theorem demorgan (P Q : Prop) : ¬ (P ∨ Q) → (¬ P ∧ ¬ Q) :=
by
  SSuffices ¬P ∧ ¬Q by intro h
  apply And.intro
  intro hP
  apply h
  left
  suffices
  SSuffices ¬Q by exact hP
  SSuffices False by intro hQ
  SSuffices P ∨ Q by apply h
  SSuffices Q by right
  exact hQ

theorem transitive_implication' (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) :=
by
  SSuffices (Q → R) → P → R by intro hPQ       -- Assume hPQ : P → Q
  SSuffices P → R by intro hQR       -- Assume hQR : Q → R
  SSuffices R by intro hp        -- Assume P
  SSuffices Q by apply hQR       -- Goal is R, use hQR : Q → R
  SSuffices P by apply hPQ       -- Goal becomes Q, use hPQ : P → Q
  exact hp         -- Conclude Q from P              -- Conclude Q from P             -- Conclude Q from P
