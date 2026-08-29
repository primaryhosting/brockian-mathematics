/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

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

lemma one_le_rad_rpow (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (1 : ℝ) ≤ (rad n : ℝ) ^ (1 + ε) :=
  Real.one_le_rpow (one_le_rad n) (by linarith)

/-- Finiteness of the exceptional sets implies the bounded form. -/
