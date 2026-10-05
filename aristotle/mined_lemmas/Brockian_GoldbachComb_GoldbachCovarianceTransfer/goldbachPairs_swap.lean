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

theorem goldbachPairs_swap (n : ℕ) :
    (goldbachPairs n).image Prod.swap = goldbachPairs n := by
  ext ⟨a, b⟩
  simp only [Finset.mem_image, mem_goldbachPairs, Prod.exists, Prod.swap_prod_mk,
    Prod.mk.injEq]
  constructor
  · rintro ⟨x, y, ⟨hx, hy, hxy⟩, rfl, rfl⟩
    exact ⟨hy, hx, by omega⟩
  · rintro ⟨hp, hq, hsum⟩
    exact ⟨b, a, ⟨hq, hp, by omega⟩, rfl, rfl⟩

