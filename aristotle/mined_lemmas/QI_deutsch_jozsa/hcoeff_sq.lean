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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

variable {n : ℕ}

/-- The sign `(-1)^b` attached to a Boolean value. -/

lemma hcoeff_sq (n : ℕ) : hcoeff n * hcoeff n = ((2 ^ n : ℝ) : ℂ)⁻¹ := by
  have h : (0 : ℝ) ≤ 2 ^ n := by positivity
  rw [hcoeff, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt h]

