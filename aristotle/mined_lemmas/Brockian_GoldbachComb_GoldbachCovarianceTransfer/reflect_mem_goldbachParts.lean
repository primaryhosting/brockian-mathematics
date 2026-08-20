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

lemma reflect_mem_goldbachParts {n p : ℕ} (hp : p ∈ goldbachParts n) :
    n - p ∈ goldbachParts n := by
  rw [mem_goldbachParts] at hp ⊢
  obtain ⟨hle, hp1, hp2⟩ := hp
  refine ⟨Nat.sub_le _ _, hp2, ?_⟩
  rwa [Nat.sub_sub_self hle]

/-- Reindexing a sum over the Goldbach parts of `n` along the reflection `p ↦ n - p`. -/
