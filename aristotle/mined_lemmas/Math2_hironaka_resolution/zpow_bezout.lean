/-
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hironaka Resolution
Category: Frontier Math
Target: Math2.hironaka_resolution
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

namespace Math2

open MvPolynomial

variable {k : Type*} [Field k]

/-- The affine plane curve `C_{p,q} : y^p = x^q`, as a polynomial in two variables. -/

lemma zpow_bezout {p q : ℕ} {a b : ℤ} (hab : a * p + b * q = 1) {t : k} (ht : t ≠ 0) :
    (t ^ p) ^ a * (t ^ q) ^ b = t := by
  rw [← zpow_natCast t p, ← zpow_natCast t q, ← zpow_mul, ← zpow_mul, ← zpow_add₀ ht]
  rw [show (p : ℤ) * a + (q : ℤ) * b = 1 by linarith [hab]]
  simp

/-- Bézout coefficients for coprime exponents. -/
