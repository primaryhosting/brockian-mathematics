import RequestProject.Loeb

/-!
# Soundness and consistency of the calculus

We interpret the language of arithmetic in the standard model `ℕ` and prove that every formula
provable in `Frontier.Provable` is true in `ℕ` under every assignment.  In particular the
calculus is consistent (`Frontier.Provable_consistent`), so the formalization of Peano
Arithmetic used for Löb's theorem is not degenerate.
-/

namespace Frontier

/-! ## The standard model -/

/-- Extend an assignment by a value for the variable bound by the outermost `∀`. -/

theorem is a plain implication, and `Frontier.derivability_conditions_satisfiable` exhibits a
concrete `□` satisfying all of them, so the statement is not vacuous).
-/

namespace Frontier

/-! ## Syntax -/

/-- Terms of the language of arithmetic `{0, S, +, *}`, with de Bruijn indexed variables. -/
inductive Trm where
  | var : ℕ → Trm
  | zero : Trm
  | succ : Trm → Trm
  | add : Trm → Trm → Trm
  | mul : Trm → Trm → Trm
  deriving DecidableEq

/-- Formulas of the language of arithmetic, with de Bruijn indexed variables.
`⊥` and `→` are primitive; the other connectives are defined below. -/
inductive Fml where
  | eq : Trm → Trm → Fml
  | bot : Fml
  | imp : Fml → Fml → Fml
  | all : Fml → Fml
  deriving DecidableEq

/-- Implication of formulas. -/
infixr:55 " ⟹ " => Fml.imp

/-- Negation, `¬φ := φ → ⊥`. -/
