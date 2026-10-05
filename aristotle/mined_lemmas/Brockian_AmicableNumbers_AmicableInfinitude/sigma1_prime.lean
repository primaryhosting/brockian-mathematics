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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The sum of the proper divisors of `n` (all divisors of `n` other than `n` itself). -/

theorem sigma1_prime {p : ℕ} (hp : p.Prime) : sigma1 p = p + 1 := by
  unfold sigma1
  rw [hp.sum_divisors]

/-! ## Thabit ibn Qurra's rule -/

/-- The Thabit condition at `k ≥ 1`: the three numbers `3·2^k - 1`, `3·2^(k+1) - 1` and
`9·2^(2k+1) - 1` are all prime. -/
