import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header comment is placed directly after the single `import Mathlib` line, since Lean 4
requires `import` commands to precede all other commands, including module docstrings.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime factors. -/

def ABCFinitenessForm : Prop := ∀ ε : ℝ, 0 < ε → (ABCExceptions ε).Finite

/-- **The abc conjecture** (constant form): for every `ε > 0` there is a constant `K` with
`c ≤ K * rad (a * b * c) ^ (1 + ε)` for all coprime triples `a + b = c` of positive integers. -/
