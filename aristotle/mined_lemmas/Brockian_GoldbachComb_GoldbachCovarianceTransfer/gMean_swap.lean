import Brockian.GoldbachComb

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
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian.GoldbachComb

/-- The set of ordered Goldbach pairs of `n`: pairs of primes `(p, q)` with `p + q = n`. -/

theorem gMean_swap (n : ℕ) (f : ℕ × ℕ → ℝ) :
    gMean n (fun pq => f pq.swap) = gMean n f := by
  unfold gMean
  congr 1
  conv_rhs => rw [← goldbachPairs_swap n]
  rw [Finset.sum_image (by intro a _ b _ h; simpa using congrArg Prod.swap h)]

