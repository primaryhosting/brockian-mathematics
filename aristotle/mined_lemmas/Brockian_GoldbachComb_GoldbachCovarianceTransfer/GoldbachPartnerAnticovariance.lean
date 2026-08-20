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

namespace Brockian
namespace GoldbachComb

/-- The set of Goldbach summands of `n`: primes `p ≤ n` such that `n - p` is also prime.
Thus `p ∈ goldbachSet n` exactly when `p + (n - p) = n` is a Goldbach decomposition of `n`. -/

theorem GoldbachPartnerAnticovariance (n : ℕ) (g : ℕ → ℝ) :
    cov (goldbachSet n) (fun p => (p : ℝ)) (fun p => g (n - p))
      = - cov (goldbachSet n) (fun p => (p : ℝ)) g := by
  have key := GoldbachCovarianceTransfer n (fun p => (p : ℝ)) g
  have hrw : cov (goldbachSet n) (fun p => ((n - p : ℕ) : ℝ)) (fun p => g (n - p))
      = cov (goldbachSet n) (fun p => (n : ℝ) - (p : ℝ)) (fun p => g (n - p)) := by
    refine cov_congr (fun p hp => ?_) (fun _ _ => rfl)
    exact Nat.cast_sub (mem_goldbachSet.mp hp).1
  rw [hrw, cov_const_sub] at key
  linarith [key]

/-- Sanity check: the Goldbach summands of `10` are `3, 5, 7`, so the covariance above is
taken over a genuinely nonempty sample. -/
