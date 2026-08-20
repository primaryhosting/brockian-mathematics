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

namespace Brockian.GoldbachComb

/-- The set of Goldbach parts of `n`: primes `p ≤ n` such that `n - p` is also prime.
Thus `p ∈ goldbachParts n` exactly when `p + (n - p) = n` is a Goldbach decomposition. -/

lemma sum_goldbachParts_reflect {M : Type*} [AddCommMonoid M] (n : ℕ) (F : ℕ → M) :
    ∑ p ∈ goldbachParts n, F (n - p) = ∑ p ∈ goldbachParts n, F p := by
  refine Finset.sum_nbij' (fun p => n - p) (fun p => n - p) ?_ ?_ ?_ ?_ ?_ <;>
    intro a ha
  · exact reflect_mem_goldbachParts ha
  · exact reflect_mem_goldbachParts ha
  · exact Nat.sub_sub_self (mem_goldbachParts.mp ha).1
  · exact Nat.sub_sub_self (mem_goldbachParts.mp ha).1
  · rfl

/-- The (empirical) covariance of two weights `f, g` over a finite index set `s`. -/
