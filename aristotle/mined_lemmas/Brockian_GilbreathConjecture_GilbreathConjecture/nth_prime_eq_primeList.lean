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

import Mathlib

/-!
# Gilbreath Conjecture
Category: Brockian Conjecture
Target: Brockian.GilbreathConjecture.GilbreathConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

namespace Brockian
namespace GilbreathConjecture

/-! ## The Gilbreath triangle and the statement of the conjecture -/

/-- `gilbreathRow n k` is the `k`-th entry (0-indexed) of the `n`-th row of the
Gilbreath triangle: row `0` is the sequence of primes `2, 3, 5, 7, 11, ...` and each
subsequent row is obtained by taking absolute values of consecutive differences. -/

theorem nth_prime_eq_primeList (k : ℕ) (hk : k < 109) :
    Nat.nth Nat.Prime k = primeList.getD k 0 := by
  have hp : ∀ i < 109, Nat.Prime (primeList.getD i 0) := by decide
  have hc : ∀ i < 109, Nat.count Nat.Prime (primeList.getD i 0) = i := by decide
  have h := Nat.nth_count (hp k hk)
  rwa [hc k hk] at h

/-- A computable model of the rows of the Gilbreath triangle, truncated to the data
provided by the first `109` primes. -/
