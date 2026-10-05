import Mathlib
import RequestProject.Frontier

/-!
# A concrete Gödel numbering, and non-vacuity of Tarski's undefinability theorem

`Frontier.Tarski_undefinability` is stated for an arbitrary *injective* Gödel numbering
`code : AForm → Nat`.  Here we exhibit such a numbering, so that the hypothesis of the

def ATerm.eval (v : Nat → Nat) : ATerm → Nat
  | .var i => v i
  | .zero => 0
  | .one => 1
  | .add t u => t.eval v + u.eval v
  | .mul t u => t.eval v * u.eval v

/-- Formulas of the language of arithmetic.  The connectives `¬`, `∧` and the existential
quantifier suffice: the other connectives and `∀` are definable from them. -/
inductive AForm : Type
  | eq : ATerm → ATerm → AForm
  | not : AForm → AForm
  | and : AForm → AForm → AForm
  | ex : Nat → AForm → AForm

/-- Update an assignment at one variable. -/
