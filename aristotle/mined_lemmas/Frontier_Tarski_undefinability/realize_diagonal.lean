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

theorem realize_diagonal (θ : arith.Formula (Fin 2)) (n : ℕ) :
    (diagonal θ).Realize ![n] ↔ ¬ θ.Realize ![n, n] := by
  have h : (![n] : Fin 1 → ℕ) ∘ (fun _ => (0 : Fin 1)) = ![n, n] := by
    funext i; fin_cases i <;> rfl
  simp [diagonal, Formula.realize_relabel, h]

/--
**Tarski's undefinability theorem.**

Fix any Gödel numbering `code` of the arithmetical formulas in one free variable.
Then the satisfaction relation for these formulas over the standard model of arithmetic
is not itself arithmetically definable: there is no set `Sat ⊆ ℕ × ℕ` which both

* correctly expresses satisfaction, i.e. `(⌜phi⌝, n) ∈ Sat ↔ ℕ ⊨ phi(n)`, and
* is arithmetical.
-/
