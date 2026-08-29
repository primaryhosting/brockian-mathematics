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

def arith : Language where
  Functions := arithFunc
  Relations := arithRel

/-- The standard model of arithmetic: the natural numbers, with the usual
interpretation of `0`, `S`, `+`, `·` and `<`. -/
instance : arith.Structure ℕ where
  funMap {n} f := match n, f with
    | _, .zero => fun _ => 0
    | _, .succ => fun v => v 0 + 1
    | _, .add => fun v => v 0 + v 1
    | _, .mul => fun v => v 0 * v 1
  RelMap {n} r := match n, r with
    | _, .lt => fun v => v 0 < v 1

/-- The numeral `S(S(...S(0)...))` (with `n` successors) as a term of the language
of arithmetic. -/
