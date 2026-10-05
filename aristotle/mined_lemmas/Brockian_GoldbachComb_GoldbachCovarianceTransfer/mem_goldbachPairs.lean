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

@[simp] theorem mem_goldbachPairs {n : ℕ} {pq : ℕ × ℕ} :
    pq ∈ goldbachPairs n ↔ Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 + pq.2 = n := by
  classical
  constructor
  · intro h
    simpa [goldbachPairs, Finset.mem_filter] using (Finset.mem_filter.mp h).2
  · rintro ⟨hp, hq, hsum⟩
    refine Finset.mem_filter.mpr ⟨?_, hp, hq, hsum⟩
    refine Finset.mem_product.mpr ⟨?_, ?_⟩ <;>
      exact Finset.mem_range.mpr (by omega)

/-- The empirical mean of `f` over the ordered Goldbach pairs of `n`
(with the convention that the mean is `0` when `n` has no Goldbach representation). -/
