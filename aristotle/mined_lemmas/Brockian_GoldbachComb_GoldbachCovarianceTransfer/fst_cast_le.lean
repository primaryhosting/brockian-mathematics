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

theorem fst_cast_le {n : ℕ} {pq : ℕ × ℕ} (h : pq ∈ goldbachPairs n) :
    ((pq.2 : ℕ) : ℝ) = (n : ℝ) - ((pq.1 : ℕ) : ℝ) := by
  have := (mem_goldbachPairs.mp h).2.2
  have : (pq.1 : ℝ) + (pq.2 : ℝ) = (n : ℝ) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) this
  linarith

/-- Covariance of a function of the first summand with a function of the second summand
equals the covariance obtained after reflecting the second summand through `n`; i.e. the
joint statistic is transferred to a statistic of the single coordinate `p`. -/
