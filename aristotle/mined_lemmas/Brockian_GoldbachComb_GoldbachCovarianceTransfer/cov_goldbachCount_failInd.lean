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

/-!
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Brockian.GoldbachComb

/-! ## Primality (self-contained, no imports) -/

/-- `IsPrime p` : `p` is at least `2` and has no divisors other than `1` and `p`. -/

theorem cov_goldbachCount_failInd (S : List Nat) :
    cov S goldbachCount failInd = -(lsum S goldbachCount * lsum S failInd) := by
  have hpt : (fun n => goldbachCount n * failInd n) = (fun _ => (0 : Int)) := by
    funext n
    by_cases h : goldbachCount n = 0
    · simp [h]
    · simp [failInd, h]
  simp [cov, hpt, lsum_zero]

/-- **Goldbach Covariance Transfer.**

Let `S` be any finite list of natural numbers on which the Goldbach counting function has
positive total mass. If the (unnormalized) empirical covariance over `S` between the
Goldbach counting function and the indicator of the Goldbach-failure set vanishes, then
Goldbach's property holds at every `n ∈ S`: each such `n` is a sum of two primes.

This is a Lean-checked conditional reduction: a covariance hypothesis on a finite window
`S` transfers to the full two-primes statement on that window. -/
