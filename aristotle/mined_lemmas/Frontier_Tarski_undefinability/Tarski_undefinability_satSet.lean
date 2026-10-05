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

theorem Tarski_undefinability_satSet (code : arith.Formula (Fin 1) → ℕ)
    (hcode : Function.Injective code) : ¬ IsArithmetical₂ (satSet code) :=
  Tarski_undefinability code (satSet code) (mem_satSet code hcode)

/-- **Tarski's undefinability theorem, "no universal formula" form.** No single formula
`θ(x, y)` of the language of arithmetic is universal for the formulas in one free variable:
there is always a formula `φ` such that no value of the parameter `x` makes `θ(x, ·)` define
the same set as `φ`. -/
