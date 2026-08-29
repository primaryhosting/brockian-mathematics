import Mathlib

/-!
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Arithmetical truth is not arithmetically definable (Tarski's undefinability theorem).

Everything is built from scratch: the syntax of first-order arithmetic (with named
variables), its satisfaction relation in the standard model `ℕ`, the notion of an
arithmetically definable set/relation, Gödel numberings, and the truth set.
-/

namespace Frontier

set_option autoImplicit false

/-! ## Syntax of first-order arithmetic -/

/-- Terms of the language of arithmetic `{0, S, +, *}`, with variables indexed by `ℕ`. -/
inductive ATerm : Type
  | var : ℕ → ATerm
  | zero : ATerm
  | succ : ATerm → ATerm
  | add : ATerm → ATerm → ATerm
  | mul : ATerm → ATerm → ATerm
  deriving DecidableEq, Encodable

/-- Formulas of the language of arithmetic.  `all i φ` is `∀ xᵢ, φ`. -/
inductive AForm : Type
  | eq : ATerm → ATerm → AForm
  | not : AForm → AForm
  | and : AForm → AForm → AForm
  | all : ℕ → AForm → AForm
  deriving DecidableEq, Encodable

instance : Inhabited AForm := ⟨AForm.eq ATerm.zero ATerm.zero⟩

/-- Evaluation of a term in the standard model `ℕ` under an assignment `ρ`. -/

def substTermNum (i k : ℕ) : ATerm → ATerm
  | .var j => if j = i then numeral k else .var j
  | .zero => .zero
  | .succ t => .succ (substTermNum i k t)
  | .add s t => .add (substTermNum i k s) (substTermNum i k t)
  | .mul s t => .mul (substTermNum i k s) (substTermNum i k t)

/-- Substitute the numeral for `k` in place of the free variable `xᵢ` in a formula. -/
