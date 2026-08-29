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

theorem gCov_congr {n : ℕ} {f₁ f₂ g₁ g₂ : ℕ × ℕ → ℝ}
    (hf : ∀ pq ∈ goldbachPairs n, f₁ pq = f₂ pq)
    (hg : ∀ pq ∈ goldbachPairs n, g₁ pq = g₂ pq) :
    gCov n f₁ g₁ = gCov n f₂ g₂ := by
  unfold gCov
  rw [gMean_congr (fun pq hpq => by rw [hf pq hpq, hg pq hpq]), gMean_congr hf,
    gMean_congr hg]

/-- The set of ordered Goldbach pairs is invariant under swapping the two summands. -/
