import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QI

/-! ## Setup

We model the Deutsch–Jozsa algorithm on `n` query bits.  A computational basis
state is an element of `Fin n → Bool`, and a (pure) state of the query register
is a function `(Fin n → Bool) → ℂ` of amplitudes. -/

variable {n : ℕ}

/-- The sign `(-1)^b` attached to a Boolean value. -/

theorem sqrt_two_pow_sq (n : ℕ) :
    ((Real.sqrt (2 ^ n) : ℝ) : ℂ) * ((Real.sqrt (2 ^ n) : ℝ) : ℂ) = (2 : ℂ) ^ n := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  push_cast
  ring

/-- The sum of the query phases equals `2^n - 2 · #{x | f x}`. -/
