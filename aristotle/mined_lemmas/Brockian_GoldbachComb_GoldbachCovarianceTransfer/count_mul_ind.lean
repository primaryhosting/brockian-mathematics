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

import Mathlib

/-!
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Classical

namespace Brockian.GoldbachComb

/-- `n` is Goldbach representable if it is a sum of two primes. -/

lemma count_mul_ind (n : ℕ) :
    (goldbachCount n : ℝ) * goldbachInd n = (goldbachCount n : ℝ) := by
  by_cases h : Representable n
  · simp [goldbachInd, h]
  · have h0 : goldbachCount n = 0 := by
      by_contra hne
      exact h ((goldbachCount_pos_iff n).mp (Nat.pos_of_ne_zero hne))
    simp [goldbachInd, h, h0]

