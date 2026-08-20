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

lemma mean_reflect (n : ℕ) (F : ℕ → ℝ) :
    mean (goldbachSet n) (fun p => F (n - p)) = mean (goldbachSet n) F := by
  unfold mean
  rw [sum_reflect]

/--
**Goldbach Covariance Transfer.**

For every `n` and every pair of real-valued statistics `f, g` on the natural numbers, the
empirical covariance of `f` and `g` over the Goldbach summands of `n` is unchanged when both
statistics are transferred to the Goldbach partner, i.e. evaluated at `n - p` instead of `p`.
-/
