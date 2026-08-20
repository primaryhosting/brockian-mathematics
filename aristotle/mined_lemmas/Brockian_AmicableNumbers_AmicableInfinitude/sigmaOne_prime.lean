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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AmicableNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/

lemma sigmaOne_prime {p : ℕ} (hp : p.Prime) : sigmaOne p = p + 1 := by
  unfold sigmaOne
  rw [hp.divisors]
  rw [Finset.sum_pair hp.one_lt.ne]
  omega

/-- **Thabit ibn Qurra's rule** (in the arithmetic-free form): if `p + 1 = 3·2^k`,
`q + 1 = 3·2^(k+1)` and `r + 1 = 9·2^(2k+1)` with `p, q, r` prime and `k ≥ 1`, then
`2^(k+1) * (p * q)` and `2^(k+1) * r` form an amicable pair. -/
