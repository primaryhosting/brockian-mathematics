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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AmicableNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The sum of all (positive) divisors of `n`.  For `n = 0` this is `0`. -/

theorem thabit_identity (k : ℕ) (A P Q R : ℤ)
    (hA : A + 1 = 2 ^ (k + 3)) (hP : P + 1 = 3 * 2 ^ (k + 1)) (hQ : Q + 1 = 3 * 2 ^ (k + 2))
    (hR : R + 1 = 9 * 2 ^ (2 * k + 3)) :
    A * ((P + 1) * (Q + 1)) = 2 ^ (k + 2) * P * Q + 2 ^ (k + 2) * R ∧
      A * (R + 1) = 2 ^ (k + 2) * P * Q + 2 ^ (k + 2) * R := by
  have e1 : (2 : ℤ) ^ (k + 1) = 2 ^ k * 2 := by ring
  have e2 : (2 : ℤ) ^ (k + 2) = 2 ^ k * 4 := by ring
  have e3 : (2 : ℤ) ^ (k + 3) = 2 ^ k * 8 := by ring
  have e4 : (2 : ℤ) ^ (2 * k + 3) = (2 ^ k) ^ 2 * 8 := by rw [two_mul, pow_add, pow_add]; ring
  rw [e1] at hP
  rw [e2] at hQ
  rw [e3] at hA
  rw [e4] at hR
  rw [e2]
  have hA' : A = 2 ^ k * 8 - 1 := by linarith
  have hP' : P = 3 * (2 ^ k * 2) - 1 := by linarith
  have hQ' : Q = 3 * (2 ^ k * 4) - 1 := by linarith
  have hR' : R = 9 * ((2 ^ k) ^ 2 * 8) - 1 := by linarith
  subst hA' hP' hQ' hR'
  constructor <;> ring

/-- **Thâbit ibn Qurra's rule.**  If `p + 1 = 3 * 2 ^ (k+1)`, `q + 1 = 3 * 2 ^ (k+2)` and
`r + 1 = 9 * 2 ^ (2k+3)` are all prime, then `(2 ^ (k+2) * p * q, 2 ^ (k+2) * r)` is an
amicable pair. -/
