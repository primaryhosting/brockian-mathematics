/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

def Exceptional (ε : ℝ) : Set (ℕ × ℕ) :=
  {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
    ((rad (p.1 * p.2 * (p.1 + p.2)) : ℝ)) ^ (1 + ε) < ((p.1 + p.2 : ℕ) : ℝ)}

/-- **The abc conjecture** (finiteness form): for every `ε > 0` there are only finitely many
coprime pairs of positive integers `a, b` with `c = a + b > rad (a * b * c) ^ (1 + ε)`. -/
