import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset

/-- A `±1` sequence, indexed by the positive integers. -/

def IsPlusMinusOne (f : ℕ → ℤ) : Prop := ∀ n, 1 ≤ n → f n = 1 ∨ f n = -1

/-- The discrepancy sum of `f` along the homogeneous arithmetic progression of common
difference `d`, truncated after `n` terms: `f d + f 2d + ⋯ + f nd`. -/
