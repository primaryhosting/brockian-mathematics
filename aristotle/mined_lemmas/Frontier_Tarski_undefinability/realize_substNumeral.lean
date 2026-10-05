/-
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the
-- header above is given as a plain block comment and repeated below verbatim.)

import Mathlib

/-!
# Tarski Undefinability
Category: Frontier — Set Theory
Target: Frontier.Tarski_undefinability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Frontier

open FirstOrder Language

/-! ## The language of arithmetic -/

/-- The function symbols of the language of arithmetic: `0`, the successor `S`,
addition and multiplication. -/
inductive arithFunc : ℕ → Type
  | zero : arithFunc 0
  | succ : arithFunc 1
  | add : arithFunc 2
  | mul : arithFunc 2
  deriving DecidableEq

/-- The relation symbols of the language of arithmetic: the order relation `<`. -/
inductive arithRel : ℕ → Type
  | lt : arithRel 2
  deriving DecidableEq

/-- The first-order language of arithmetic, `(0, S, +, ·, <)`. -/

theorem realize_substNumeral (φ : arith.Formula (Fin 1)) (n : ℕ) :
    (ℕ ⊨ substNumeral φ n) ↔ φ.Realize ![n] := by
  rw [Sentence.Realize, substNumeral, Formula.realize_subst]
  have : (fun a : Fin 1 => Term.realize (default : Empty → ℕ) (numeral n : arith.Term Empty))
      = ![n] := by
    funext i; fin_cases i; simp
  rw [this]

/--
**Tarski's undefinability theorem for the set of true sentences.**

Suppose we are given Gödel numberings `codeF` of the formulas in one free variable and
`codeS` of the sentences, together with a substitution function `sub` computing the code of
`φ(n̄)` from the code of `φ` and the number `n`, and suppose (as holds for every reasonable
coding) that the graph of `sub` is arithmetical.

Then the set of (codes of) true sentences of arithmetic is not arithmetical: arithmetical
truth is not arithmetically definable.
-/
