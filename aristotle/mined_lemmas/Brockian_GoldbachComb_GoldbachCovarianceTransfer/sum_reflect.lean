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

lemma sum_reflect (n : ℕ) (F : ℕ → ℝ) :
    ∑ p ∈ goldbachSet n, F (n - p) = ∑ p ∈ goldbachSet n, F p := by
  refine Finset.sum_nbij' (i := fun p => n - p) (j := fun p => n - p)
    (fun a ha => reflect_mem_goldbachSet ha) (fun a ha => reflect_mem_goldbachSet ha)
    (fun a ha => ?_) (fun a ha => ?_) (fun a _ => rfl)
  · exact Nat.sub_sub_self (mem_goldbachSet.mp ha).1
  · exact Nat.sub_sub_self (mem_goldbachSet.mp ha).1

/-- Means over the Goldbach set are invariant under the reflection `p ↦ n - p`. -/
